import OddMath.Frontier.OddCyclotomicActionF

/-!
# `K₀(ONH^N)` is the integral form of the irreducible `U_q(sl_2)`-module `V(N)`

EKL arXiv:1111.1320v1, §6, last paragraph (p. 47): `ONH^N = ⊕_{a=0}^{N} ONH_a^N`; the graded
Grothendieck group `K₀(ONH^N)` has the size of the integral form `V(N)_A` of the irreducible
`U_q(sl_2)`-module of highest weight `N`, and the functors given by the bimodules
`ONH_{a+1}^N` (the odd analogues of the cohomology of two-step flag varieties) descend to the action
of `E` and `F`.

Here `A = ℤ[q,q⁻¹]`, `q = T 1` acting on `K₀` by the grading shift `{1}`, and
`w_a = [E^{(a)}] = [ONH_a^N e_a {C(a,2)}]` (`cycBasis`), `0 ≤ a ≤ N`.

* `EN`: induction along `ONH_a^N → ONH_{a+1}^N` (`OddBialgebra.EN`):
  `E w_a = [a+1] w_{a+1}`, `E w_N = 0`.
* `FN`: restriction along `ONH_a^N → ONH_{a+1}^N`, shifted by `{λ - 1}` on the summand of weight
  `λ = 2(a+1) - N` (`cycF`): `F w_{a+1} = [N-a] w_a`, `F w_0 = 0` (`FN_cycBasis`,
  `FN_cycBasis_zero`).
* `KN`: `K w_a = q^{2a-N} w_a`; `w_0` is a lowest weight vector.
* **The `U_q(sl_2)` relations** on `K₀(ONH^N)`: `K K⁻¹ = K⁻¹ K = 1`, `K E = q² E K`,
  `K F = q⁻² F K`, and `(q - q⁻¹)(EF - FE) = K - K⁻¹` (`KN_EN`, `KN_FN`, `sl2_relation`);
  on the weight space of weight `2a - N`, `EF - FE = [2a - N]` (`commutator_cycBasis`).
* **Divided powers**: the operators `E^{(k)}`, `F^{(k)}` with `[k]! E^{(k)} = E^k`,
  `[k]! F^{(k)} = F^k` preserve `K₀(ONH^N)` (`qFact_smul_EdivN`, `qFact_smul_FdivN`).
* **`K₀(ONH^N) ≅ V(N)_A`** (`cycIso`): the isomorphism `w_a ↦ e_a = E^{(a)} v_{-N}` onto the
  standard model `VN N = A^{N+1}` of `V(N)_A`, intertwining `E`, `F`, `K` and the divided powers
  (`cycIso_EN`, `cycIso_FN`, `cycIso_KN`, `cycIso_EdivN`, `cycIso_FdivN`).

Deviation from the paper's wording: restriction along `ONH_a^N → ONH_{a+1}^N` gives
`Res w_{a+1} = q^{N-2a-1} [N-a] w_a`; `F` is restriction followed by the grading shift `{λ - 1}`
(as in the even case, the bimodules defining `F` carry weight-dependent shifts). The weight
convention is that `w_0 = [ONH_0^N]` has weight `-N`.
-/

noncomputable section
open LaurentPolynomial

namespace OddMath.Frontier.OddCyclotomicAction
open GradedK0 OddCategorification Cyclotomic OddBialgebra QuantumSl2Plus

local notation "L" => LaurentPolynomial ℤ

/-! ### `F` on `K₀(ONH^N)` -/

/-- `F` out of the summand `K₀(ONH_a^N)`. -/
def Fdown (N : ℕ) : (a : ℕ) → KCyc N a →ₗ[L] K0Cyc N
  | 0 => 0
  | a+1 => if h : a < N then (DFinsupp.lsingle (⟨a, by omega⟩ : Fin (N+1))).comp (cycF N a h)
      else 0

/-- `F` on `K₀(ONH^N) = ⊕_a K₀(ONH_a^N)`: restriction `K₀(ONH_{a+1}^N) → K₀(ONH_a^N)` along
`ONH_a^N → ONH_{a+1}^N` in each weight, shifted by `{λ - 1}`. -/
def FN (N : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  DFinsupp.lsum L fun a : Fin (N+1) => Fdown N a

/-- **`F` on `K₀(ONH^N)`**: `F [E^{(a+1)}] = [N-a] [E^{(a)}]`. -/
theorem FN_cycBasis (N a : ℕ) (ha : a < N) :
    FN N (cycBasis N ⟨a+1, by omega⟩) = qInt (N - a) • cycBasis N ⟨a, by omega⟩ := by
  rw [cycBasis_apply, cycBasis_apply, FN, DFinsupp.lsum_single]
  show Fdown N (a+1) (vCyc N (a+1)) = _
  rw [Fdown, dif_pos ha, LinearMap.comp_apply, cycF_vCyc, DFinsupp.lsingle_apply,
    DFinsupp.single_smul]

/-- `F [E^{(0)}] = 0`. -/
theorem FN_cycBasis_zero (N : ℕ) : FN N (cycBasis N 0) = 0 := by
  rw [cycBasis_apply, FN, DFinsupp.lsum_single]
  rfl

/-! ### `K` -/

/-- `K = q^{2a-N}` on `K₀(ONH_a^N)`. -/
def KN (N : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  DFinsupp.mapRange.linearMap fun a : Fin (N+1) =>
    (T (2 * (a : ℤ) - N) : L) • (LinearMap.id : KCyc N a →ₗ[L] KCyc N a)

/-- `K⁻¹ = q^{N-2a}` on `K₀(ONH_a^N)`. -/
def KNinv (N : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  DFinsupp.mapRange.linearMap fun a : Fin (N+1) =>
    (T ((N : ℤ) - 2 * (a : ℤ)) : L) • (LinearMap.id : KCyc N a →ₗ[L] KCyc N a)

theorem KN_cycBasis (N : ℕ) (a : Fin (N+1)) :
    KN N (cycBasis N a) = (T (2 * (a : ℤ) - N) : L) • cycBasis N a := by
  rw [cycBasis_apply, KN, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single,
    LinearMap.smul_apply, LinearMap.id_apply, DFinsupp.single_smul]

theorem KNinv_cycBasis (N : ℕ) (a : Fin (N+1)) :
    KNinv N (cycBasis N a) = (T ((N : ℤ) - 2 * (a : ℤ)) : L) • cycBasis N a := by
  rw [cycBasis_apply, KNinv, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single,
    LinearMap.smul_apply, LinearMap.id_apply, DFinsupp.single_smul]

/-! ### The `U_q(sl_2)` relations -/

theorem KN_KNinv (N : ℕ) : KN N ∘ₗ KNinv N = LinearMap.id :=
  (cycBasis N).ext fun a => by
    rw [LinearMap.comp_apply, KNinv_cycBasis, map_smul, KN_cycBasis, smul_smul, ← T_add,
      show (N : ℤ) - 2 * a + (2 * a - N) = 0 by ring, T_zero, one_smul, LinearMap.id_apply]

theorem KNinv_KN (N : ℕ) : KNinv N ∘ₗ KN N = LinearMap.id :=
  (cycBasis N).ext fun a => by
    rw [LinearMap.comp_apply, KN_cycBasis, map_smul, KNinv_cycBasis, smul_smul, ← T_add,
      show 2 * (a : ℤ) - N + (N - 2 * a) = 0 by ring, T_zero, one_smul, LinearMap.id_apply]

/-- `K E = q² E K`. -/
theorem KN_EN (N : ℕ) : KN N ∘ₗ EN N = (T 2 : L) • (EN N ∘ₗ KN N) :=
  (cycBasis N).ext fun a => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, KN_cycBasis, map_smul]
    by_cases ha : (a : ℕ) < N
    · rw [EN_cycBasis N a ha, map_smul, KN_cycBasis, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [← T_add, mul_comm]
      congr 2
      simp only [Fin.val_mk]
      push_cast
      ring
    · obtain rfl : a = Fin.last N := Fin.ext (by have := a.isLt; simp; omega)
      rw [EN_cycBasis_last, map_zero, smul_zero, smul_zero]

/-- `K F = q⁻² F K`. -/
theorem KN_FN (N : ℕ) : KN N ∘ₗ FN N = (T (-2) : L) • (FN N ∘ₗ KN N) :=
  (cycBasis N).ext fun a => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, KN_cycBasis, map_smul]
    rcases a with ⟨_ | a, ha⟩
    · rw [show (⟨0, ha⟩ : Fin (N+1)) = 0 from rfl, FN_cycBasis_zero, map_zero, smul_zero,
        smul_zero]
    · rw [FN_cycBasis N a (by omega), map_smul, KN_cycBasis, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [← T_add, mul_comm]
      congr 2
      simp only [Fin.val_mk]
      push_cast
      ring

/-- The quantum integer `[m]` for `m ∈ ℤ`, `[-m] = -[m]`. -/
def qIntZ (m : ℤ) : L := if 0 ≤ m then qInt m.toNat else -qInt (-m).toNat

theorem qIntZ_mul (m : ℤ) : (T 1 - T (-1) : L) * qIntZ m = T m - T (-m) := by
  rw [qIntZ]
  split_ifs with h
  · rw [qInt_mul, Int.toNat_of_nonneg h]
  · rw [mul_neg, qInt_mul, Int.toNat_of_nonneg (by omega), neg_neg, neg_sub]

theorem T_one_sub_ne_zero : (T 1 - T (-1) : L) ≠ 0 := by
  intro h
  have := T_injective (sub_eq_zero.1 h)
  omega

/-- `(q - q⁻¹)([a][M+1] - [a+1][M]) = q^{a-M} - q^{M-a}`. -/
theorem qInt_commutator (a M : ℕ) :
    (T 1 - T (-1) : L) * (qInt a * qInt (M+1) - qInt (a+1) * qInt M) =
      T ((a : ℤ) - M) - T ((M : ℤ) - a) := by
  refine mul_left_cancel₀ T_one_sub_ne_zero ?_
  have h1 := qInt_mul a
  have h2 := qInt_mul (M+1)
  have h3 := qInt_mul (a+1)
  have h4 := qInt_mul M
  calc (T 1 - T (-1) : L) * ((T 1 - T (-1)) * (qInt a * qInt (M+1) - qInt (a+1) * qInt M))
      = ((T 1 - T (-1)) * qInt a) * ((T 1 - T (-1)) * qInt (M+1)) -
          ((T 1 - T (-1)) * qInt (a+1)) * ((T 1 - T (-1)) * qInt M) := by ring
    _ = (T (a : ℤ) - T (-(a : ℤ))) * (T ((M+1 : ℕ) : ℤ) - T (-((M+1 : ℕ) : ℤ))) -
          (T ((a+1 : ℕ) : ℤ) - T (-((a+1 : ℕ) : ℤ))) * (T (M : ℤ) - T (-(M : ℤ))) := by
        rw [h1, h2, h3, h4]
    _ = (T 1 - T (-1)) * (T ((a : ℤ) - M) - T ((M : ℤ) - a)) := by
        simp only [sub_mul, mul_sub, ← T_add]
        push_cast
        ring_nf

/-- `EF w_a = [a][N-a+1] w_a`. -/
theorem EN_FN_cycBasis (N : ℕ) (a : Fin (N+1)) :
    EN N (FN N (cycBasis N a)) = (qInt a * qInt (N - a + 1)) • cycBasis N a := by
  rcases a with ⟨_ | a, ha⟩
  · rw [show (⟨0, ha⟩ : Fin (N+1)) = 0 from rfl, FN_cycBasis_zero, map_zero]
    simp
  · rw [FN_cycBasis N a (by omega), map_smul, EN_cycBasis N ⟨a, by omega⟩ (by simp; omega),
      smul_smul]
    congr 1
    rw [mul_comm]
    congr 2
    simp only [Fin.val_mk]
    omega

/-- `FE w_a = [a+1][N-a] w_a`. -/
theorem FN_EN_cycBasis (N : ℕ) (a : Fin (N+1)) :
    FN N (EN N (cycBasis N a)) = (qInt (a+1) * qInt (N - a)) • cycBasis N a := by
  by_cases ha : (a : ℕ) < N
  · rw [EN_cycBasis N a ha, map_smul, FN_cycBasis N a ha, smul_smul]
  · obtain rfl : a = Fin.last N := Fin.ext (by have := a.isLt; simp; omega)
    rw [EN_cycBasis_last, map_zero, Fin.val_last, Nat.sub_self, qInt_zero, mul_zero, zero_smul]

/-- **`EF - FE = [2a - N]`** on the weight space `K₀(ONH_a^N)` of weight `2a - N`. -/
theorem commutator_cycBasis (N : ℕ) (a : Fin (N+1)) :
    EN N (FN N (cycBasis N a)) - FN N (EN N (cycBasis N a)) =
      qIntZ (2 * (a : ℤ) - N) • cycBasis N a := by
  rw [EN_FN_cycBasis, FN_EN_cycBasis, ← sub_smul]
  congr 1
  refine mul_left_cancel₀ T_one_sub_ne_zero ?_
  have h := qInt_commutator a (N - a)
  have hN : ((N - a : ℕ) : ℤ) = (N : ℤ) - a := by have := a.isLt; omega
  rw [qIntZ_mul, h, hN]
  congr 1 <;> congr 1 <;> ring

/-- **The `U_q(sl_2)` relation** `(q - q⁻¹)(EF - FE) = K - K⁻¹` on `K₀(ONH^N)`. -/
theorem sl2_relation (N : ℕ) :
    (T 1 - T (-1) : L) • (EN N ∘ₗ FN N - FN N ∘ₗ EN N) = KN N - KNinv N :=
  (cycBasis N).ext fun a => by
    rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      commutator_cycBasis, smul_smul, qIntZ_mul, LinearMap.sub_apply, KN_cycBasis,
      KNinv_cycBasis, ← sub_smul]
    congr 2
    ring_nf

/-! ### Divided powers -/

/-- `E^{(k)} w_a = [a+k, a] w_{a+k}`. -/
def EdivN (N k : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  (cycBasis N).constr L fun a =>
    if h : (a : ℕ) + k ≤ N then qBinom a k • cycBasis N ⟨a + k, by omega⟩ else 0

/-- `F^{(k)} w_{a+k} = [N-a, k] w_a`. -/
def FdivN (N k : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  (cycBasis N).constr L fun a =>
    if h : k ≤ (a : ℕ) then qBinom k (N - a) • cycBasis N ⟨a - k, by omega⟩ else 0

theorem EdivN_cycBasis (N k : ℕ) (a : Fin (N+1)) :
    EdivN N k (cycBasis N a) =
      if h : (a : ℕ) + k ≤ N then qBinom a k • cycBasis N ⟨a + k, by omega⟩ else 0 :=
  (cycBasis N).constr_basis L _ a

theorem FdivN_cycBasis (N k : ℕ) (a : Fin (N+1)) :
    FdivN N k (cycBasis N a) =
      if h : k ≤ (a : ℕ) then qBinom k (N - a) • cycBasis N ⟨a - k, by omega⟩ else 0 :=
  (cycBasis N).constr_basis L _ a

/-- `[a+k, a] [k]! [a+k+1] = [a+k+1, a] [k+1]!`. -/
theorem qBinom_step (a k : ℕ) :
    qBinom a k * qFact k * qInt (a + k + 1) = qBinom a (k+1) * qFact (k+1) := by
  refine mul_left_cancel₀ (qFact_ne_zero a) ?_
  calc qFact a * (qBinom a k * qFact k * qInt (a + k + 1))
      = (qBinom a k * qFact a * qFact k) * qInt (a + k + 1) := by ring
    _ = qFact (a + (k+1)) := by rw [qBinom_mul_qFact, ← add_assoc, qFact_succ]
    _ = qFact a * (qBinom a (k+1) * qFact (k+1)) := by rw [← qBinom_mul_qFact]; ring

theorem EN_pow_cycBasis (N k : ℕ) (a : Fin (N+1)) :
    (EN N ^ k) (cycBasis N a) = qFact k • EdivN N k (cycBasis N a) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_apply, EdivN_cycBasis, dif_pos (by omega), qBinom_comm,
      qBinom_zero_left, one_smul]
    simp [qFact]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, EdivN_cycBasis, EdivN_cycBasis]
    by_cases h : (a : ℕ) + (k + 1) ≤ N
    · rw [dif_pos (by omega : (a : ℕ) + k ≤ N), dif_pos h, map_smul, map_smul,
        EN_cycBasis N ⟨a + k, by omega⟩ (by simp; omega), smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_mk]
      rw [mul_comm (qFact (k+1)), ← qBinom_step]
      ring
    · by_cases h' : (a : ℕ) + k ≤ N
      · have hlast : (⟨a + k, by omega⟩ : Fin (N+1)) = Fin.last N := Fin.ext (by simp; omega)
        rw [dif_pos h', dif_neg h, map_smul, map_smul, hlast, EN_cycBasis_last, smul_zero,
          smul_zero, smul_zero]
      · rw [dif_neg h', dif_neg h, smul_zero, map_zero, smul_zero]

/-- **`E^k = [k]! E^{(k)}`**: the divided powers of `E` preserve `K₀(ONH^N)`. -/
theorem qFact_smul_EdivN (N k : ℕ) : qFact k • EdivN N k = EN N ^ k :=
  (cycBasis N).ext fun a => by rw [LinearMap.smul_apply, EN_pow_cycBasis]

theorem FN_pow_cycBasis (N k : ℕ) (a : Fin (N+1)) :
    (FN N ^ k) (cycBasis N a) = qFact k • FdivN N k (cycBasis N a) := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_apply, FdivN_cycBasis, dif_pos (Nat.zero_le _),
      qBinom_zero_left, one_smul]
    simp [qFact]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, FdivN_cycBasis, FdivN_cycBasis]
    by_cases h : k + 1 ≤ (a : ℕ)
    · rw [dif_pos (by omega : k ≤ (a : ℕ)), dif_pos h, map_smul, map_smul]
      have hb : (⟨(a : ℕ) - k, by omega⟩ : Fin (N+1)) = ⟨(a - (k+1)) + 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [hb, FN_cycBasis N (a - (k+1)) (by omega), smul_smul, smul_smul, smul_smul]
      congr 1
      · have e : N - (a - (k+1)) = N - a + k + 1 := by omega
        rw [e, qBinom_comm k, qBinom_comm (k+1), mul_comm (qFact (k+1)), ← qBinom_step]
        ring
    · by_cases h' : k ≤ (a : ℕ)
      · have h0 : (⟨(a : ℕ) - k, by omega⟩ : Fin (N+1)) = 0 := Fin.ext (by simp; omega)
        rw [dif_pos h', dif_neg h, map_smul, map_smul, h0, FN_cycBasis_zero, smul_zero,
          smul_zero, smul_zero]
      · rw [dif_neg h', dif_neg h, smul_zero, map_zero, smul_zero]

/-- **`F^k = [k]! F^{(k)}`**: the divided powers of `F` preserve `K₀(ONH^N)`. -/
theorem qFact_smul_FdivN (N k : ℕ) : qFact k • FdivN N k = FN N ^ k :=
  (cycBasis N).ext fun a => by rw [LinearMap.smul_apply, FN_pow_cycBasis]

/-! ### `K₀(ONH^N) ≅ V(N)_A` -/

/-- The standard model of the integral form `V(N)_A` of the irreducible `U_q(sl_2)`-module of
highest weight `N`: the free `A`-module on `e_a = E^{(a)} v_{-N}`, `0 ≤ a ≤ N`, with
`E e_a = [a+1] e_{a+1}`, `F e_a = [N-a+1] e_{a-1}`, `K e_a = q^{2a-N} e_a`,
`E^{(k)} e_a = [a+k, a] e_{a+k}`, `F^{(k)} e_a = [N-a+k, k] e_{a-k}`. -/
abbrev VN (N : ℕ) : Type := Fin (N+1) → L

/-- `e_a` -/
abbrev vn (N : ℕ) (a : Fin (N+1)) : VN N := Pi.single a 1

/-- `E` on `V(N)_A`. -/
def stdE (N : ℕ) : VN N →ₗ[L] VN N :=
  (Pi.basisFun L (Fin (N+1))).constr L fun a =>
    if h : (a : ℕ) < N then qInt (a + 1) • vn N ⟨a + 1, by omega⟩ else 0

/-- `F` on `V(N)_A`. -/
def stdF (N : ℕ) : VN N →ₗ[L] VN N :=
  (Pi.basisFun L (Fin (N+1))).constr L fun a =>
    if h : 0 < (a : ℕ) then qInt (N - a + 1) • vn N ⟨a - 1, by omega⟩ else 0

/-- `K` on `V(N)_A`. -/
def stdK (N : ℕ) : VN N →ₗ[L] VN N :=
  (Pi.basisFun L (Fin (N+1))).constr L fun a => (T (2 * (a : ℤ) - N) : L) • vn N a

/-- `E^{(k)}` on `V(N)_A`. -/
def stdEdiv (N k : ℕ) : VN N →ₗ[L] VN N :=
  (Pi.basisFun L (Fin (N+1))).constr L fun a =>
    if h : (a : ℕ) + k ≤ N then qBinom a k • vn N ⟨a + k, by omega⟩ else 0

/-- `F^{(k)}` on `V(N)_A`. -/
def stdFdiv (N k : ℕ) : VN N →ₗ[L] VN N :=
  (Pi.basisFun L (Fin (N+1))).constr L fun a =>
    if h : k ≤ (a : ℕ) then qBinom k (N - a) • vn N ⟨a - k, by omega⟩ else 0

/-- **`K₀(ONH^N) ≅ V(N)_A`**, `[E^{(a)}] ↦ E^{(a)} v_{-N}`. -/
def cycIso (N : ℕ) : K0Cyc N ≃ₗ[L] VN N :=
  (cycBasis N).equiv (Pi.basisFun L (Fin (N+1))) (Equiv.refl _)

theorem cycIso_cycBasis (N : ℕ) (a : Fin (N+1)) : cycIso N (cycBasis N a) = vn N a := by
  rw [cycIso, Basis.equiv_apply, Equiv.refl_apply, Pi.basisFun_apply]

theorem constr_vn (N : ℕ) (f : Fin (N+1) → VN N) (a : Fin (N+1)) :
    (Pi.basisFun L (Fin (N+1))).constr L f (vn N a) = f a := by
  have h : vn N a = Pi.basisFun L (Fin (N+1)) a := (Pi.basisFun_apply L (Fin (N+1)) a).symm
  rw [h, Basis.constr_basis]

/-- `K₀(ONH^N) ≅ V(N)_A` intertwines `E`. -/
theorem cycIso_EN (N : ℕ) : cycIso N ∘ₗ EN N = stdE N ∘ₗ (cycIso N).toLinearMap :=
  (cycBasis N).ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cycIso_cycBasis, stdE, constr_vn]
    by_cases ha : (a : ℕ) < N
    · rw [EN_cycBasis N a ha, map_smul, cycIso_cycBasis, dif_pos ha]
    · obtain rfl : a = Fin.last N := Fin.ext (by have := a.isLt; simp; omega)
      rw [EN_cycBasis_last, map_zero, dif_neg ha]

/-- `K₀(ONH^N) ≅ V(N)_A` intertwines `F`. -/
theorem cycIso_FN (N : ℕ) : cycIso N ∘ₗ FN N = stdF N ∘ₗ (cycIso N).toLinearMap :=
  (cycBasis N).ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cycIso_cycBasis, stdF, constr_vn]
    rcases a with ⟨_ | a, ha⟩
    · rw [show (⟨0, ha⟩ : Fin (N+1)) = 0 from rfl, FN_cycBasis_zero, map_zero, dif_neg (by simp)]
    · rw [FN_cycBasis N a (by omega), map_smul, cycIso_cycBasis, dif_pos (by simp)]
      congr 1
      simp only [Fin.val_mk]
      congr 1
      omega

/-- `K₀(ONH^N) ≅ V(N)_A` intertwines `K`. -/
theorem cycIso_KN (N : ℕ) : cycIso N ∘ₗ KN N = stdK N ∘ₗ (cycIso N).toLinearMap :=
  (cycBasis N).ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cycIso_cycBasis, stdK, constr_vn]
    rw [KN_cycBasis, map_smul, cycIso_cycBasis]

/-- `K₀(ONH^N) ≅ V(N)_A` intertwines `E^{(k)}`. -/
theorem cycIso_EdivN (N k : ℕ) :
    cycIso N ∘ₗ EdivN N k = stdEdiv N k ∘ₗ (cycIso N).toLinearMap :=
  (cycBasis N).ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cycIso_cycBasis, stdEdiv, constr_vn]
    rw [EdivN_cycBasis]
    split_ifs
    · rw [map_smul, cycIso_cycBasis]
    · rw [map_zero]

/-- `K₀(ONH^N) ≅ V(N)_A` intertwines `F^{(k)}`. -/
theorem cycIso_FdivN (N k : ℕ) :
    cycIso N ∘ₗ FdivN N k = stdFdiv N k ∘ₗ (cycIso N).toLinearMap :=
  (cycBasis N).ext fun a => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cycIso_cycBasis, stdFdiv, constr_vn]
    rw [FdivN_cycBasis]
    split_ifs
    · rw [map_smul, cycIso_cycBasis]
    · rw [map_zero]

end OddMath.Frontier.OddCyclotomicAction
