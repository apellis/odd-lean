import OddMath.Frontier.EKOverKBases
import OddMath.Frontier.EKOverKHopf
import OddMath.Frontier.EKGeneralQSpecial
import OddMath.Frontier.EKCompleteKostka
import OddMath.Frontier.EKInfiniteSymmetry

/-!
# EK §1 and §2.3 over `k`: the role of `2 ∈ k`

Source: Ellis–Khovanov, arXiv:1107.5610v2.  EK work over an arbitrary commutative ring `k`
(p. 5) and put `q = -1` from §2.2 on.  If `2 = 0` in `k` then `q = -1 = 1`, so
`Λ_k = Λ_{1,k}` is the classical (commutative) ring.  Several claims of §1 and §2.3 therefore
hold exactly when `2 ≠ 0` in `k`.  For each claim we prove an `iff`, and the failure over `𝔽₂`.

* §1 p. 3, "`Λ` is neither commutative nor cocommutative":
  `commutative_iff`, `cocommutative_iff`, `supercommutative_iff`: `Λ_k` is commutative
  (resp. cocommutative, supercommutative) iff `2 = 0` in `k`.
* §2.3 p. 19, ψ₂ is not the identity: `psi2K_eq_one_iff`.
* §2.3 p. 19, "ψ₁ is not an involution": `psi1K_involutive_iff`.
* Prop. 2.17, "`S² ≠ 1`": `SK_involutive_iff`.
* §2.3 p. 19, "`ψ₃(e_n) ≠ e_n`" (`n ≥ 2`): `psi3K_e_iff`.
* `psi3K_eq_id_iff`: ψ₃ is the identity iff `2 = 0`.

The failures over `𝔽₂ = ZMod 2` are `F2_*`; `Z_not_commutative`, `Z_not_cocommutative` are
the claims of §1 over `ℤ`.  The order of ψ₁ and the group `⟨ψ₁, ψ₂⟩` are
treated in `EKOverKOrder`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ
open EKAutomorphisms (s)

variable {k : Type*} [CommRing k]

/-! ## Arithmetic of `2` and `-1` -/

theorem two_eq_zero_iff_neg_one_eq_one : (2 : k) = 0 ↔ (-1 : k) = 1 := by
  constructor
  · intro h; rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h]
  · intro h
    have h' : (1 : k) + 1 = -1 + 1 := by rw [h]
    rw [neg_add_cancel, one_add_one_eq_two] at h'
    exact h'

theorem neg_one_pow_of_two (h2 : (2 : k) = 0) (n : ℕ) : (-1 : k) ^ n = 1 := by
  rw [two_eq_zero_iff_neg_one_eq_one.mp h2, one_pow]

theorem s_cast_of_two (h2 : (2 : k) = 0) (n : ℕ) : ((s n : ℤ) : k) = 1 := by
  simp only [s, Int.cast_pow, Int.cast_neg, Int.cast_one, neg_one_pow_of_two h2]

/-! ## Some `h`-basis vectors -/

/-- The Young diagram with the given (weakly decreasing, positive) row lengths. -/
def yd (l : List ℕ) (hl : l.Sorted (· ≥ ·)) : YoungDiagram := YoungDiagram.ofRowLens l hl

theorem hBasisK_yd (l : List ℕ) (hl : l.Sorted (· ≥ ·)) (hpos : ∀ a ∈ l, 0 < a) :
    hBasisK (k := k) (yd l hl) = (l.map (hK k)).prod := by
  rw [hBasisK_apply, yd, YoungDiagram.rowLens_ofRowLens_eq_self hpos, hWord, map_list_prod,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact (hK_eq a).symm

/-- `h₁h₁ = h_{(1,1)}`. -/
def yd11 : YoungDiagram := yd [1, 1] (by decide)
/-- `h₂h₁ = h_{(2,1)}`. -/
def yd21 : YoungDiagram := yd [2, 1] (by decide)
/-- `h₃ = h_{(3)}`. -/
def yd3 : YoungDiagram := yd [3] (by decide)

theorem hBasisK_yd11 : hBasisK (k := k) yd11 = hK k 1 * hK k 1 := by
  rw [yd11, hBasisK_yd _ _ (by decide)]; simp

theorem hBasisK_yd21 : hBasisK (k := k) yd21 = hK k 2 * hK k 1 := by
  rw [yd21, hBasisK_yd _ _ (by decide)]; simp

theorem hBasisK_yd3 : hBasisK (k := k) yd3 = hK k 3 := by
  rw [yd3, hBasisK_yd _ _ (by decide)]; simp

theorem yd21_ne_yd3 : yd21 ≠ yd3 := by
  intro h
  have := congrArg YoungDiagram.rowLens h
  rw [yd21, yd3, yd, yd, YoungDiagram.rowLens_ofRowLens_eq_self (by decide),
    YoungDiagram.rowLens_ofRowLens_eq_self (by decide)] at this
  simp at this

/-- A scalar multiple of an `h`-basis vector vanishes only for the zero scalar. -/
theorem smul_hBasisK_eq_zero {c : k} {μ : YoungDiagram} (h : c • hBasisK (k := k) μ = 0) :
    c = 0 := by
  have := congrArg (fun x => (hBasisK (k := k)).repr x μ) h
  simp only [map_smul, Basis.repr_self, map_zero, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.coe_zero, Pi.zero_apply] at this
  exact this

theorem two_eq_zero_of_two_smul_h11 (h : (2 : k) • (hK k 1 * hK k 1) = 0) : (2 : k) = 0 := by
  rw [← hBasisK_yd11] at h
  exact smul_hBasisK_eq_zero h

/-! ## Commutativity and cocommutativity -/

/-- (2.12) with `a = 2`, `b = 1` over `k`: `h₂h₁ + h₁h₂ = 2h₃`. -/
theorem h2h1_add_h1h2 : hK k 2 * hK k 1 + hK k 1 * hK k 2 = (2 : k) • hK k 3 := by
  have h := congrArg (psiRing (k := k)) (EKAutomorphisms.h_odd 2 0 (by decide))
  simp only [map_add, psiRing_zsmul, map_mul] at h
  norm_num at h
  rw [two_smul]
  have h0 : psiRing (k := k) (EKElementaryQuotient.h 0) = 1 := hK_zero
  rw [h0, mul_one, one_mul] at h
  exact h

/-- If `2 = 0` in `k`, then `Λ_k` is commutative (it is `Λ_{1,k}`). -/
theorem mul_comm_of_two (h2 : (2 : k) = 0) (x y : LamK k) : x * y = y * x := by
  have h : (-1 : k) = 1 := two_eq_zero_iff_neg_one_eq_one.mp h2
  revert x y
  change ∀ x y : Lam (-1 : k), x * y = y * x
  rw [h]
  exact lam_one_mul_comm

/-- **EK §1 over `k`:** `Λ_k` is commutative iff `2 = 0` in `k`.  In particular `Λ_k` is not
commutative whenever `2 ≠ 0` in `k` (e.g. over `ℤ`, `ℚ`, or `𝔽_p`, `p` odd). -/
theorem commutative_iff : (∀ x y : LamK k, x * y = y * x) ↔ (2 : k) = 0 := by
  refine ⟨fun hc => ?_, fun h2 => mul_comm_of_two h2⟩
  have h := h2h1_add_h1h2 (k := k)
  rw [hc (hK k 1), ← two_smul k, ← hBasisK_yd21, ← hBasisK_yd3] at h
  have := congrArg (fun x => (hBasisK (k := k)).repr x yd21) h
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne yd21_ne_yd3.symm, smul_eq_mul, mul_one, mul_zero] at this
  exact this

/-- `Λ_k` is supercommutative (`xy = (-1)^{|x||y|} yx` on homogeneous elements) iff `2 = 0`. -/
theorem supercommutative_iff :
    (∀ (a b : ℕ) (x y : LamK k), x ∈ degreePieceK k a → y ∈ degreePieceK k b →
      x * y = ((-1 : k) ^ (a * b)) • (y * x)) ↔ (2 : k) = 0 := by
  constructor
  · intro hc
    have h1 : hK k 1 ∈ degreePieceK k 1 := by
      rw [hK]; exact psi_degreePiece (by simpa using EKAutomorphisms.hWord_degree [1])
    have := hc 1 1 _ _ h1 h1
    rw [pow_one, neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul k] at this
    exact two_eq_zero_of_two_smul_h11 this
  · intro h2 a b x y _ _
    rw [neg_one_pow_of_two h2, one_smul, mul_comm_of_two h2]

/-- Dual pairing of the flip of a tensor. -/
theorem tensorTest_comm (a b : LamK k) (z : LamK k ⊗[k] LamK k) :
    tensorTest (-1 : k) a b (TensorProduct.comm k _ _ z) = tensorTest (-1 : k) b a z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero]
  | tmul x y => rw [TensorProduct.comm_tmul, tensorTest_tmul, tensorTest_tmul, mul_comm]
  | add u v hu hv => rw [LinearEquiv.map_add, LinearMap.map_add, hu, hv, LinearMap.map_add]

/-- **EK §1 over `k`:** `Λ_k` is cocommutative (plain flip) iff `2 = 0` in `k`.  The proof
is by duality: `(a ⊗ b, Δx) = (ab, x)` and the form is nondegenerate, so cocommutativity is
equivalent to commutativity. -/
theorem cocommutative_iff :
    (∀ x : LamK k, TensorProduct.comm k _ _ (coproductK x) = coproductK x) ↔ (2 : k) = 0 := by
  rw [← commutative_iff]
  constructor
  · intro hc a b
    rw [← sub_eq_zero]
    apply quotientForm_nondegenerate_left (-1 : k)
    intro x
    have h1 := EKFinal.tensorTest_coproductK a b x
    have h2 := EKFinal.tensorTest_coproductK b a x
    rw [← hc x, tensorTest_comm] at h1
    rw [map_sub, LinearMap.sub_apply, ← h1, ← h2, sub_self]
  · intro hc x
    rw [← sub_eq_zero]
    apply separating_neg_one
    intro a b
    rw [map_sub, tensorTest_comm]
    change tensorTest (-1 : k) b a (coproductK x) - tensorTest (-1 : k) a b (coproductK x) = 0
    rw [EKFinal.tensorTest_coproductK, EKFinal.tensorTest_coproductK, hc, sub_self]

/-! ## ψ₂ and ψ₃ are the identity iff `2 = 0` -/

theorem psiRing_psi2_of_two (h2 : (2 : k) = 0) (z : QZ) :
    psiRing (k := k) (EKAutomorphisms.psi2 z) = psiRing z := by
  have h : (psiRing (k := k)).comp EKAutomorphisms.psi2.toRingHom = psiRing := by
    apply EKAutomorphisms.hom_ext_h
    intro n
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      EKAutomorphisms.psi2_h, psiRing_zsmul, s_cast_of_two h2, one_smul]
  exact RingHom.congr_fun h z

/-- ψ₂ is the identity of `Λ_k` iff `2 = 0` in `k`. -/
theorem psi2K_eq_one_iff : psi2K k = 1 ↔ (2 : k) = 0 := by
  constructor
  · intro h
    have := congrArg (fun f : LamK k ≃ₐ[k] LamK k => f (hK k 1)) h
    simp only [psi2K_h, AlgEquiv.one_apply] at this
    have hs : ((s 1 : ℤ) : k) = -1 := by simp [s]
    rw [hs, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul k] at this
    apply smul_hBasisK_eq_zero (μ := yd11)
    rw [hBasisK_yd11]
    have h' := congrArg (· * hK k 1) this
    simp only [smul_mul_assoc, zero_mul] at h'
    exact h'
  · intro h2
    apply algEquiv_ext
    intro z
    rw [psi2K_psiRing, psiRing_psi2_of_two h2]
    rfl

theorem list_prod_reverse_of_comm {M : Type*} [Monoid M] (hc : ∀ x y : M, x * y = y * x)
    (l : List M) : l.reverse.prod = l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.reverse_cons, List.prod_append, ih, List.prod_singleton,
      List.prod_cons, hc]

theorem piQ_hWord_eq (l : List ℕ) : piQ (-1 : k) (hWord k l) = (l.map (hK k)).prod := by
  rw [hWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact (hK_eq a).symm

/-- ψ₃ is the identity of `Λ_k` iff `2 = 0` in `k`. -/
theorem psi3K_eq_id_iff : psi3K k = LinearMap.id ↔ (2 : k) = 0 := by
  constructor
  · intro h
    have := LinearMap.congr_fun h (eK' k 2)
    have hc := congrArg (bcChar k EKComplete.chi) this
    rw [LinearMap.id_apply, psi3K, eK', bcLin_psiRing, bcChar_psiRing, bcChar_psiRing] at hc
    change ((EKComplete.fpsi 2 : ℤ) : k) = _ at hc
    rw [EKComplete.fpsi_eq, EKComplete.chi_e] at hc
    norm_num at hc
    exact hc
  · intro h2
    apply (hBasisK (k := k)).ext
    intro μ
    rw [LinearMap.id_apply, hBasisK_apply, piQ_hWord_eq, psi3K_hWord, neg_one_pow_of_two h2,
      one_smul, List.map_reverse, list_prod_reverse_of_comm (mul_comm_of_two h2)]

/-- **EK p. 19 over `k`:** for `n ≥ 2`, `ψ₃(e_n) = e_n` iff `2 = 0` in `k`.  (For `n ≤ 1`,
`ψ₃(e_n) = e_n` always.) -/
theorem psi3K_e_iff (n : ℕ) : psi3K k (eK' k n) = eK' k n ↔ n ≤ 1 ∨ (2 : k) = 0 := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    right
    have hc := congrArg (bcChar k EKComplete.chi) h
    rw [psi3K, eK', bcLin_psiRing, bcChar_psiRing, bcChar_psiRing] at hc
    change ((EKComplete.fpsi n : ℤ) : k) = _ at hc
    rw [EKComplete.fpsi_eq, EKComplete.chi_e, if_neg hn, if_neg hn] at hc
    norm_num at hc
    exact hc
  · rintro (hn | h2)
    · rw [eK', psi3K, bcLin_psiRing]
      exact congrArg psiRing ((EKComplete.psi3_e_fixed_iff n).mpr hn)
    · rw [psi3K_eq_id_iff.mpr h2, LinearMap.id_apply]

/-! ## ψ₁ and the antipode -/

theorem psi1K_psi1K_h2 :
    psi1K k (psi1K k (hK k 2)) = hK k 2 - (2 : k) • (hK k 1 * hK k 1) := by
  rw [hK, psi1K_psiRing, psi1K_psiRing, EKPresentationControls.psi1_square_degree_two, map_sub,
    psiRing_zsmul, map_mul]
  push_cast; rfl

/-- **EK p. 19 over `k`:** ψ₁ is an involution of `Λ_k` iff `2 = 0` in `k`. -/
theorem psi1K_involutive_iff : (∀ x : LamK k, psi1K k (psi1K k x) = x) ↔ (2 : k) = 0 := by
  constructor
  · intro h
    have := h (hK k 2)
    rw [psi1K_psi1K_h2, sub_eq_self] at this
    exact two_eq_zero_of_two_smul_h11 this
  · intro h2 x
    have h1 : ∀ y, psi2K k y = y := fun y => by rw [psi2K_eq_one_iff.mpr h2]; rfl
    have := psi12K_involutive x
    rw [psi12K_apply, psi12K_apply, h1, h1] at this
    exact this

theorem SK_SK_h2 : SK k (SK k (hK k 2)) = hK k 2 - (2 : k) • (hK k 1 * hK k 1) := by
  rw [hK, SK_psiRing, SK_psiRing, EKAntipode.S_square_h_two, map_sub, psiRing_zsmul, map_mul]
  push_cast; rfl

/-- **EK Prop. 2.17 over `k`:** `S² = 1` iff `2 = 0` in `k`; so `S² ≠ 1` exactly when
`2 ≠ 0`. -/
theorem SK_involutive_iff : (∀ x : LamK k, SK k (SK k x) = x) ↔ (2 : k) = 0 := by
  constructor
  · intro h
    have := h (hK k 2)
    rw [SK_SK_h2, sub_eq_self] at this
    exact two_eq_zero_of_two_smul_h11 this
  · intro h2 x
    have h1 : ∀ y, psi2K k y = y := fun y => by rw [psi2K_eq_one_iff.mpr h2]; rfl
    have h3 : ∀ y, psi3K k y = y := fun y => by rw [psi3K_eq_id_iff.mpr h2]; rfl
    rw [SK_apply, SK_apply, h3, h1, h3, h1]
    exact psi1K_involutive_iff.mpr h2 x

/-! ## The failures over `𝔽₂` -/

theorem two_eq_zero_F2 : (2 : ZMod 2) = 0 := by decide

/-- Over `𝔽₂`, `Λ` is commutative (EK §1 claims it is not). -/
theorem F2_commutative : ∀ x y : LamK (ZMod 2), x * y = y * x :=
  commutative_iff.mpr two_eq_zero_F2

/-- Over `𝔽₂`, `Λ` is supercommutative. -/
theorem F2_supercommutative (a b : ℕ) (x y : LamK (ZMod 2)) (hx : x ∈ degreePieceK (ZMod 2) a)
    (hy : y ∈ degreePieceK (ZMod 2) b) : x * y = ((-1 : ZMod 2) ^ (a * b)) • (y * x) :=
  supercommutative_iff.mpr two_eq_zero_F2 a b x y hx hy

/-- Over `𝔽₂`, `Λ` is cocommutative (EK §1 claims it is not). -/
theorem F2_cocommutative (x : LamK (ZMod 2)) :
    TensorProduct.comm (ZMod 2) _ _ (coproductK x) = coproductK x :=
  cocommutative_iff.mpr two_eq_zero_F2 x

/-- Over `𝔽₂`, ψ₂ is the identity. -/
theorem F2_psi2K : psi2K (ZMod 2) = 1 := psi2K_eq_one_iff.mpr two_eq_zero_F2

/-- Over `𝔽₂`, ψ₁ is an involution (EK p. 19 claims it is not). -/
theorem F2_psi1K_involutive (x : LamK (ZMod 2)) : psi1K (ZMod 2) (psi1K (ZMod 2) x) = x :=
  psi1K_involutive_iff.mpr two_eq_zero_F2 x

/-- Over `𝔽₂`, `S² = 1` (Prop. 2.17 claims `S² ≠ 1`). -/
theorem F2_SK_involutive (x : LamK (ZMod 2)) : SK (ZMod 2) (SK (ZMod 2) x) = x :=
  SK_involutive_iff.mpr two_eq_zero_F2 x

/-- Over `𝔽₂`, ψ₃ is the identity; in particular `ψ₃(e_n) = e_n` for every `n`. -/
theorem F2_psi3K_e (n : ℕ) : psi3K (ZMod 2) (eK' (ZMod 2) n) = eK' (ZMod 2) n :=
  (psi3K_e_iff n).mpr (Or.inr two_eq_zero_F2)

/-! ## The case `k = ℤ` -/

theorem two_ne_zero_int : (2 : ℤ) ≠ 0 := by decide

/-- Over `ℤ`, `Λ` is not commutative (EK §1). -/
theorem Z_not_commutative : ¬ ∀ x y : LamK ℤ, x * y = y * x :=
  fun h => two_ne_zero_int (commutative_iff.mp h)

/-- Over `ℤ`, `Λ` is not cocommutative (EK §1). -/
theorem Z_not_cocommutative :
    ¬ ∀ x : LamK ℤ, TensorProduct.comm ℤ _ _ (coproductK x) = coproductK x :=
  fun h => two_ne_zero_int (cocommutative_iff.mp h)

end OddMath.Frontier.EKOverK
