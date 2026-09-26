import OddMath.Frontier.OddBialgebraCorner
import OddMath.Frontier.OnhStructure
import OddMath.Frontier.CyclotomicGraded

/-!
# `K₀(ONH_a ⊗ ONH_b) ≅ ℤ[q,q⁻¹]`

EKL arXiv:1111.1320v1, §6, pp. 46–47. Here `a = m+2`, `b = m'+2`,
`B = ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` (`OnhStructure.tensorImage`) with the grading `gradB`.

* `projector_mul_mul_projector_neg`, `projector_mul_mul_projector_zero`: the corner
  `e_a ONH_a e_a ≅ OΛ_a` vanishes in negative degrees and is `ℤ e_a` in degree `0`
  (through `e_a y e_a = e_a (-1)^{C(a,3)} (D_a(y(x^δ)))^{w₀} e_a`).
* `eB = e_a ⊗ e_b`, an idempotent of degree `0`, and `splitB`: `1 = ∑ σ̃ λ̃` with
  `λ̃_x σ̃_y = δ_{xy} (e_a ⊗ e_b)`, the tensor product of the splittings (6.1) of `ONH_a` and
  `ONH_b` (with the Koszul sign on `λ̃`).
* `cornerB_connected`: the corner `(e_a ⊗ e_b) B (e_a ⊗ e_b)` is connected.
* `K0B.classify : K₀(B) ≃ ℤ[q,q⁻¹]`, `[B(e_a ⊗ e_b){k}] ↦ q^k`; `[E^{(a)} ⊠ E^{(b)}]` is a basis
  (`K0B.basis`).
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open GradedK0 NilCoxeterWords NilHeckeAction NilHeckeBasis OnhStructure OnhWindow
  OddCategorification QuantumSl2Plus ZeroHecke NilHeckeGradedEnd
open OddMath.SkewPolynomial (SkewPolynomial)

/-! ### The corner `e_a ONH_a e_a` -/

section OnhCorner

variable {n : ℕ}

theorem piece_of_eq {N : ℕ} {d d' : ℤ} {f : SkewPolynomial N} (h : f ∈ polynomialPiece N d)
    (e : d = d') : f ∈ polynomialPiece N d' := e ▸ h

theorem cornerPre_mem {j : ℤ} {y : Presented n} (hy : y ∈ onhGrading n (2 * j)) :
    cornerPre y ∈ polynomialPiece (n+2) (2 * j) := by
  have h1 : action n y (LongestDivided.staircase (n+2)) ∈
      ProjectorRank.Vd (n+2) ((((n+2).choose 2 : ℕ) : ℤ) + j) :=
    piece_of_eq (action_mem hy (staircase_mem (n+2))) (by ring)
  have h2 := ProjectorRank.hasDegree_D (n := n) _ _ h1
  have h3 : (⟨_, LongestKernel.D_mem_kernel n (action n y (LongestDivided.staircase (n+2)))⟩ :
      K n) ∈ OddCategorification.kerGrading n (2 * j) :=
    piece_of_eq h2 (by ring)
  have h4 := (Cyclotomic.revK_mem_kerGrading_iff n (2 * j) _).2 h3
  exact Submodule.smul_mem _ _ h4

theorem thick_intCast (z : ℤ) : thick n (z : SkewPolynomial (n+2)) = z • projector n := by
  rw [thick, map_intCast, mul_assoc, (Int.cast_commute z _).eq, ← mul_assoc,
    projector_mul_projector, zsmul_eq_mul, (Int.cast_commute z _).eq]

/-- The corner `e_a ONH_a e_a` vanishes in negative degrees. -/
theorem projector_mul_mul_projector_neg {d : ℤ} {y : Presented n} (hy : y ∈ onhGrading n d)
    (hd : d < 0) : projector n * y * projector n = 0 := by
  by_cases h0 : y = 0
  · rw [h0, mul_zero, zero_mul]
  obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j := by
    obtain ⟨j, hj⟩ := onh_even hy h0
    exact ⟨j, by omega⟩
  have h := cornerPre_mem hy
  rw [polynomial_negative _ _ hd] at h
  rw [← thick_cornerPre, (Submodule.mem_bot ℤ).1 h, thick, map_zero, mul_zero, zero_mul]

/-- The corner `e_a ONH_a e_a` is `ℤ e_a` in degree `0`. -/
theorem projector_mul_mul_projector_zero {y : Presented n} (hy : y ∈ onhGrading n 0) :
    ∃ z : ℤ, projector n * y * projector n = z • projector n := by
  have h := cornerPre_mem (j := 0) (by rwa [mul_zero])
  rw [mul_zero] at h
  refine ⟨cornerPre y 0, ?_⟩
  rw [← thick_cornerPre]
  conv_lhs => rw [eq_intCast_of_mem h]
  exact thick_intCast _

end OnhCorner

/-! ### Degree-zero commutation -/

section Comm

variable {R₁ R₂ S : Type*} [Ring R₁] [Ring R₂] [Ring S] {A₁ : ℤ → AddSubgroup R₁}
  {A₂ : ℤ → AddSubgroup R₂} {B : ℤ → AddSubgroup S} (P : SuperPair A₁ A₂ B)

theorem SuperPair.comm_zero_right {i : ℤ} {x : R₁} {y : R₂} (hx : x ∈ A₁ (2 * i))
    (hy : y ∈ A₂ 0) : P.ι₂ y * P.ι₁ x = P.ι₁ x * P.ι₂ y := by
  have := P.comm hx (show y ∈ A₂ (2 * 0) by rwa [mul_zero])
  rwa [mul_zero, Int.negOnePow_zero, one_smul] at this

theorem SuperPair.comm_zero_left {j : ℤ} {x : R₁} {y : R₂} (hx : x ∈ A₁ 0)
    (hy : y ∈ A₂ (2 * j)) : P.ι₂ y * P.ι₁ x = P.ι₁ x * P.ι₂ y := by
  have := P.comm (show x ∈ A₁ (2 * 0) by rwa [mul_zero]) hy
  rwa [zero_mul, Int.negOnePow_zero, one_smul] at this

end Comm

/-! ### The idempotent `e_a ⊗ e_b` and the splitting of `1` -/

section Split

variable (m m' : ℕ)


/-- `e_a ⊗ e_b ∈ B`. -/
def eB : tensorImage m m' := (pairB m m').ι₁ (projector m) * (pairB m m').ι₂ (projector m')

theorem eB_val : (eB m m' : Presented (m+2+m')) =
    incL m m' (projector m) * incR m m' (projector m') := rfl

theorem projector_mem' (n : ℕ) : projector n ∈ onhGrading n (2 * 0) :=
  mem_of_deg_eq (projector_mem n) (by ring)

theorem eB_idem : IsIdempotentElem (eB m m') := by
  show (pairB m m').ι₁ (projector m) * (pairB m m').ι₂ (projector m') *
    ((pairB m m').ι₁ (projector m) * (pairB m m').ι₂ (projector m')) = _
  rw [mul_assoc, ← mul_assoc ((pairB m m').ι₂ _), (pairB m m').comm_zero_left (projector_mem m)
    (projector_mem' m'), mul_assoc, ← mul_assoc ((pairB m m').ι₁ _), ← map_mul, ← map_mul,
    projector_mul_projector, projector_mul_projector]
  rfl

theorem eB_mem : eB m m' ∈ gradB m m' 0 :=
  mem_of_deg_eq (SetLike.GradedMul.mul_mem ((pairB m m').map₁ (projector_mem m))
    ((pairB m m').map₂ (projector_mem m'))) (by ring)

instance : Fact (eB m m' ∈ gradB m m' 0) := ⟨eB_mem m m'⟩

/-- The index set `Sq(a) × Sq(b)`. -/
abbrev IdxB := BoxPartitionCount.Sq (m+2) × BoxPartitionCount.Sq (m'+2)

variable {m m'}

/-- The degree `2(|ℓ| - C(a,2)) + 2(|ℓ'| - C(b,2))` of `σ̃_{(ℓ,ℓ')}`. -/
def dB (x : IdxB m m') : ℤ :=
  2 * Categorification.deg61 x.1.1 + 2 * Categorification.deg61 x.2.1

/-- The Koszul sign of `λ̃`. -/
def sgnB (x : IdxB m m') : ℤˣ :=
  (Categorification.deg61 x.1.1 * Categorification.deg61 x.2.1).negOnePow

theorem sig_mem {n : ℕ} (ℓ : BoxPartitionCount.Sq (n+2)) :
    (Categorification.split61 n).σ ℓ ∈ onhGrading n (2 * Categorification.deg61 ℓ.1) :=
  sigma61_mem (Categorification.mem_Sq' ℓ)

theorem lam_mem {n : ℕ} (ℓ : BoxPartitionCount.Sq (n+2)) :
    (Categorification.split61 n).lam ℓ ∈ onhGrading n (2 * -Categorification.deg61 ℓ.1) :=
  mem_of_deg_eq (lam61_mem (Categorification.mem_Sq' ℓ)) (by ring)

variable (m m')

/-- The splitting `1 = ∑_{(ℓ,ℓ')} σ̃ λ̃` of `B` through `e_a ⊗ e_b`: the tensor product of the
splittings (6.1) of `ONH_a` and `ONH_b`. -/
def splitB : Categorification.Splitting (1 : tensorImage m m') (eB m m') (IdxB m m') where
  σ x := (pairB m m').ι₁ ((Categorification.split61 m).σ x.1) *
    (pairB m m').ι₂ ((Categorification.split61 m').σ x.2)
  lam x := sgnB x • ((pairB m m').ι₁ ((Categorification.split61 m).lam x.1) *
    (pairB m m').ι₂ ((Categorification.split61 m').lam x.2))
  sum_eq := by
    have hterm : ∀ x : IdxB m m',
        (pairB m m').ι₁ ((Categorification.split61 m).σ x.1) *
          (pairB m m').ι₂ ((Categorification.split61 m').σ x.2) *
          (sgnB x • ((pairB m m').ι₁ ((Categorification.split61 m).lam x.1) *
            (pairB m m').ι₂ ((Categorification.split61 m').lam x.2))) =
        (pairB m m').ι₁ ((Categorification.split61 m).σ x.1 *
            (Categorification.split61 m).lam x.1) *
          (pairB m m').ι₂ ((Categorification.split61 m').σ x.2 *
            (Categorification.split61 m').lam x.2) := by
      intro x
      rw [mul_smul_comm, mul_assoc, ← mul_assoc ((pairB m m').ι₂ _),
        (pairB m m').comm (lam_mem x.1) (sig_mem x.2), smul_mul_assoc, mul_smul_comm, smul_smul,
        sgnB, ← Int.negOnePow_add,
        show Categorification.deg61 x.1.1 * Categorification.deg61 x.2.1 +
          -Categorification.deg61 x.1.1 * Categorification.deg61 x.2.1 = 0 by ring,
        Int.negOnePow_zero, one_smul, map_mul, map_mul]
      simp only [mul_assoc]
    simp only [hterm]
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum,
      (Categorification.split61 m).sum_eq, (Categorification.split61 m').sum_eq, map_one,
      map_one, one_mul]
  orth x y := by
    have e : ∀ (a b : Presented m) (c d : Presented m'),
        (pairB m m').ι₁ a * ((pairB m m').ι₁ b * (pairB m m').ι₂ c * (pairB m m').ι₂ d) =
          (pairB m m').ι₁ (a * b) * (pairB m m').ι₂ (c * d) := fun a b c d => by
      rw [map_mul, map_mul]; simp only [mul_assoc]
    rw [smul_mul_assoc, mul_assoc, ← mul_assoc ((pairB m m').ι₂ _), (pairB m m').comm
      (sig_mem y.1) (lam_mem x.2), smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc,
      mul_assoc ((pairB m m').ι₁ _), e, (Categorification.split61 m).orth,
      (Categorification.split61 m').orth]
    by_cases h1 : x.1 = y.1
    · by_cases h2 : x.2 = y.2
      · have hxy : x = y := Prod.ext h1 h2
        subst hxy
        rw [if_pos rfl, if_pos rfl, if_pos rfl, sgnB, ← Int.negOnePow_add,
          show Categorification.deg61 x.1.1 * Categorification.deg61 x.2.1 +
            Categorification.deg61 x.1.1 * -Categorification.deg61 x.2.1 = 0 by ring,
          Int.negOnePow_zero, one_smul]
        rfl
      · rw [if_neg h2, map_zero, mul_zero, smul_zero, if_neg (fun h => h2 (congrArg Prod.snd h))]
    · rw [if_neg h1, map_zero, zero_mul, smul_zero, if_neg (fun h => h1 (congrArg Prod.fst h))]
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

theorem splitB_sigma_mem (x : IdxB m m') : (splitB m m').σ x ∈ gradB m m' (dB x) :=
  SetLike.GradedMul.mul_mem ((pairB m m').map₁ (sig_mem x.1)) ((pairB m m').map₂ (sig_mem x.2))

theorem splitB_lam_mem (x : IdxB m m') : (splitB m m').lam x ∈ gradB m m' (-dB x) :=
  units_smul_mem _ (mem_of_deg_eq (SetLike.GradedMul.mul_mem ((pairB m m').map₁ (lam_mem x.1))
    ((pairB m m').map₂ (lam_mem x.2))) (by simp only [dB]; ring))

end Split

/-! ### The corner `(e_a ⊗ e_b) B (e_a ⊗ e_b)` is connected -/

section Sandwich

variable {m m' : ℕ}

/-- Degree-`d` condition on a corner element: zero for `d < 0`, a multiple of `e_a ⊗ e_b` for
`d = 0`. -/
def CornerCond (m m' : ℕ) (d : ℤ) (v : tensorImage m m') : Prop :=
  (d < 0 → v = 0) ∧ (d = 0 → ∃ z : ℤ, v = z • eB m m')

theorem CornerCond.zero (d : ℤ) : CornerCond m m' d 0 :=
  ⟨fun _ => rfl, fun _ => ⟨0, by rw [zero_smul]⟩⟩

theorem CornerCond.add {d : ℤ} {v w : tensorImage m m'} (hv : CornerCond m m' d v)
    (hw : CornerCond m m' d w) : CornerCond m m' d (v + w) := by
  refine ⟨fun hd => by rw [hv.1 hd, hw.1 hd, add_zero], fun hd => ?_⟩
  obtain ⟨z, hz⟩ := hv.2 hd
  obtain ⟨z', hz'⟩ := hw.2 hd
  exact ⟨z + z', by rw [hz, hz', add_smul]⟩

theorem CornerCond.smul {d : ℤ} {v : tensorImage m m'} (hv : CornerCond m m' d v) (c : ℤ) :
    CornerCond m m' d (c • v) := by
  refine ⟨fun hd => by rw [hv.1 hd, smul_zero], fun hd => ?_⟩
  obtain ⟨z, hz⟩ := hv.2 hd
  exact ⟨c * z, by rw [hz, smul_smul]⟩

theorem comm_assoc {M : Type*} [Semigroup M] {a b : M} (h : a * b = b * a) (X : M) :
    a * (b * X) = b * (a * X) := by
  rw [← mul_assoc, h, mul_assoc]

theorem eB_sandwich_tensor {i j : ℤ} {x : Presented m} {x' : Presented m'}
    (hx : x ∈ onhGrading m (2 * i)) (hx' : x' ∈ onhGrading m' (2 * j)) :
    eB m m' * ((pairB m m').ι₁ x * (pairB m m').ι₂ x') * eB m m' =
      (pairB m m').ι₁ (projector m * x * projector m) *
        (pairB m m').ι₂ (projector m' * x' * projector m') := by
  have h1 := (pairB m m').comm_zero_right hx (projector_mem m')
  have h2 := (pairB m m').comm_zero_left (projector_mem m) hx'
  have h3 := (pairB m m').comm_zero_left (projector_mem m) (projector_mem' m')
  simp only [eB, map_mul, mul_assoc]
  rw [comm_assoc h1, comm_assoc h2, comm_assoc h3]

theorem cornerCond_tensor {w w' : ℤ} {x : Presented m} {x' : Presented m'}
    (hx : x ∈ onhGrading m w) (hx' : x' ∈ onhGrading m' w') (hw : Even w) (hw' : Even w') :
    CornerCond m m' (w + w') (eB m m' * ((pairB m m').ι₁ x * (pairB m m').ι₂ x') * eB m m') := by
  obtain ⟨i, rfl⟩ : ∃ i, w = 2 * i := by obtain ⟨i, hi⟩ := hw; exact ⟨i, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, w' = 2 * j := by obtain ⟨j, hj⟩ := hw'; exact ⟨j, by omega⟩
  rw [eB_sandwich_tensor hx hx']
  have zl : 2 * i < 0 → projector m * x * projector m = 0 :=
    projector_mul_mul_projector_neg hx
  have zr : 2 * j < 0 → projector m' * x' * projector m' = 0 :=
    projector_mul_mul_projector_neg hx'
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases lt_or_le (2 * i) 0 with h | h
    · rw [zl h, map_zero, zero_mul]
    · rw [zr (by omega), map_zero, mul_zero]
  · rcases lt_trichotomy (2 * i) 0 with h | h | h
    · exact ⟨0, by rw [zl h, map_zero, zero_mul, zero_smul]⟩
    · obtain ⟨z, hz⟩ := projector_mul_mul_projector_zero (h ▸ hx)
      obtain ⟨z', hz'⟩ := projector_mul_mul_projector_zero
        (show x' ∈ onhGrading m' 0 by rw [show (0 : ℤ) = 2 * j by omega]; exact hx')
      refine ⟨z * z', ?_⟩
      rw [hz, hz', map_zsmul, map_zsmul, smul_mul_smul_comm]
      rfl
    · exact ⟨0, by rw [zr (by omega), map_zero, mul_zero, zero_smul]⟩

/-- The PBW index `(A ⊔ A', w × v)` of `x^A ∂_w ⊗ x^{A'} ∂_v`. -/
def tIndex (p : ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m')) :
    (Fin (m+2+m'+2) → ℕ) × Perm (m+2+m') :=
  (appendExp p.1.1 p.2.1, blockPerm p.1.2 p.2.2)

theorem weight_tIndex (p : ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m')) :
    NilHeckeGrading.weight (tIndex p) =
      NilHeckeGrading.weight p.1 + NilHeckeGrading.weight p.2 := by
  simp only [NilHeckeGrading.weight, tIndex, sum_appendExp, length_blockPerm]
  push_cast
  ring

theorem even_weight {n : ℕ} (i : (Fin (n+2) → ℕ) × Perm n) : Even (NilHeckeGrading.weight i) :=
  ⟨(∑ j, i.1 j : ℕ) - (length i.2 : ℤ), by simp only [NilHeckeGrading.weight]; ring⟩

theorem mem_span_weight {n : ℕ} {d : ℤ} {y : Presented n} (hy : y ∈ onhGrading n d) :
    y ∈ Submodule.span ℤ (basis n '' {i | NilHeckeGrading.weight i = d}) := by
  have h : y ∈ NilHeckeGrading.leftPiece n d := by
    rw [← NilHeckeGrading.degreePiece_eq_leftPiece]; exact hy
  refine Submodule.span_mono ?_ h
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  exact ⟨i, hi, basis_apply i⟩

theorem repr_tensorMap_basis (p q : ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m'))
    (hpq : q ≠ p) :
    (basis (m+2+m')).repr (tensorMap m m' (basis m q.1 ⊗ₜ basis m' q.2)) (tIndex p) = 0 := by
  have hne : tIndex q ≠ tIndex p := fun h => hpq (blockIndex_injective h)
  rw [tensorMap_tmul, basis_apply, basis_apply]
  rcases incL_mul_incR_basis q.1.1 q.1.2 q.2.1 q.2.2 with h | h <;> rw [h]
  · rw [← basis_apply, Basis.repr_self, Finsupp.single_apply]
    exact if_neg hne
  · rw [map_neg, ← basis_apply, Basis.repr_self, Finsupp.neg_apply, Finsupp.single_apply,
      neg_eq_zero]
    exact if_neg hne

theorem repr_tensorMap_basis_self
    (p : ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m')) :
    (basis (m+2+m')).repr (tensorMap m m' (basis m p.1 ⊗ₜ basis m' p.2)) (tIndex p) ≠ 0 := by
  rw [tensorMap_tmul, basis_apply, basis_apply]
  rcases incL_mul_incR_basis p.1.1 p.1.2 p.2.1 p.2.2 with h | h <;> rw [h]
  · rw [← basis_apply, Basis.repr_self, Finsupp.single_apply]
    simp [tIndex]
  · rw [map_neg, ← basis_apply, Basis.repr_self, Finsupp.neg_apply, Finsupp.single_apply]
    simp [tIndex]

/-- **The corner `(e_a ⊗ e_b) B (e_a ⊗ e_b)` vanishes in negative degrees and is `ℤ (e_a ⊗ e_b)` in
degree `0`.** -/
theorem cornerCond_sandwich {d : ℤ} {y : tensorImage m m'} (hy : y ∈ gradB m m' d) :
    CornerCond m m' d (eB m m' * y * eB m m') := by
  obtain ⟨t, ht⟩ := y.2
  set bT := (basis m).tensorProduct (basis m')
  set c := bT.repr t
  have ht' : (y : Presented (m+2+m')) =
      ∑ q ∈ c.support, c q • tensorMap m m' (basis m q.1 ⊗ₜ basis m' q.2) := by
    rw [← ht]
    conv_lhs => rw [← bT.linearCombination_repr t]
    rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_zsmul, Basis.tensorProduct_apply]
  have hy' : y = ∑ q ∈ c.support,
      c q • ((pairB m m').ι₁ (basis m q.1) * (pairB m m').ι₂ (basis m' q.2)) := by
    apply Subtype.ext
    rw [ht']
    push_cast
    rfl
  -- only the tensors of total weight `d` occur
  have hw : ∀ q ∈ c.support,
      NilHeckeGrading.weight q.1 + NilHeckeGrading.weight q.2 = d := by
    intro p hp
    rw [← weight_tIndex]
    have hsupp := (Basis.mem_span_image (basis (m+2+m'))).1
      (mem_span_weight (show (y : Presented (m+2+m')) ∈ onhGrading _ d from hy))
    refine hsupp (Finsupp.mem_support_iff.2 ?_)
    rw [ht', map_sum, Finsupp.finset_sum_apply]
    simp only [map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single p (fun q _ hq => by rw [repr_tensorMap_basis p q hq, mul_zero])
      (fun h => absurd hp h)]
    exact mul_ne_zero (Finsupp.mem_support_iff.1 hp) (repr_tensorMap_basis_self p)
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_induction _ (CornerCond m m' d) (fun _ _ => CornerCond.add)
    (CornerCond.zero d) fun q hq => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  refine CornerCond.smul ?_ _
  have := cornerCond_tensor (m := m) (m' := m')
    (show basis m q.1 ∈ onhGrading m (NilHeckeGrading.weight q.1) by
      rw [basis_apply]; exact NilHeckeGrading.basisElement_mem q.1)
    (show basis m' q.2 ∈ onhGrading m' (NilHeckeGrading.weight q.2) by
      rw [basis_apply]; exact NilHeckeGrading.basisElement_mem q.2)
    (even_weight q.1) (even_weight q.2)
  rwa [hw q hq] at this

end Sandwich

/-! ### Connectedness and the classification -/

section Classify

variable (m m' : ℕ)

theorem eB_val_blockE : (eB m m' : Presented (m+2+m')) =
    ThickBubble.blockE (m+2+m') 0 (m+2) * ThickBubble.blockE (m+2+m') (m+2) (m'+2) := by
  rw [eB_val, ThickBubble.blockE_eq (window_left_le m m'),
    ThickBubble.blockE_eq (window_right_le m m')]
  rfl

theorem eB_ne_zero : (eB m m' : Presented (m+2+m')) ≠ 0 := by
  intro h
  rw [eB_val_blockE] at h
  let S := Categorification.split62 (n := m+2+m') (a := m+2) (b := m'+2) (by omega)
  have hα : (fun _ : Fin (m+2) => 0) ∈ BoxPartitionCount.box (m+2) (m'+2) :=
    BoxPartitionCount.mem_box.2 ⟨fun _ _ _ => le_rfl, fun _ => Nat.zero_le _⟩
  let α : BoxPartitionCount.box (m+2) (m'+2) := ⟨_, hα⟩
  have h1 : S.lam α = 0 :=
    ((S.lam_mul α).symm.trans (congrArg (S.lam α * ·) h)).trans (mul_zero _)
  have h2 := S.orth α α
  rw [if_pos rfl, h1, zero_mul] at h2
  exact OnhStructure.projector_ne_zero (m+2+m') h2.symm

theorem zsmul_eB_injective {z w : ℤ} (h : z • eB m m' = w • eB m m') : z = w := by
  have h' : z • (eB m m' : Presented (m+2+m')) = w • (eB m m' : Presented (m+2+m')) :=
    congrArg Subtype.val h
  rw [← sub_eq_zero, ← sub_smul, (basis (m+2+m')).smul_eq_zero] at h'
  rcases h' with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' (eB_ne_zero m m')

/-- **The corner `(e_a ⊗ e_b) B (e_a ⊗ e_b)` is connected.** -/
theorem cornerB_connected : Connected (cornerGrading (gradB m m') (eB_idem m m')) where
  neg d hd x hx := by
    have h := (cornerCond_sandwich hx).1 hd
    rw [mul_assoc, cval_apply, corner_right, corner_left] at h
    exact Subtype.ext h
  zero x hx := by
    obtain ⟨z, hz⟩ := (cornerCond_sandwich hx).2 rfl
    rw [mul_assoc, cval_apply, corner_right, corner_left] at hz
    refine ⟨z, Subtype.ext ?_⟩
    rw [hz, ← zsmul_one, ← cval_apply, map_zsmul]
    rfl
  inj z w h := by
    have h' := congrArg (cval (eB_idem m m')) h
    rw [← zsmul_one, ← zsmul_one w, map_zsmul, map_zsmul] at h'
    exact zsmul_eB_injective m m' h'

/-- **`K₀(ONH_a ⊗ ONH_b) ≅ ℤ[q,q⁻¹]`**, `[B(e_a ⊗ e_b){k}] ↦ q^k`. -/
def K0B.classify : K0 (gradB m m') ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  K0.cornerClassify (splitB m m') (splitB_sigma_mem m m') (splitB_lam_mem m m')
    (cornerB_connected m m')

theorem K0B.classify_gelem (k : ℤ) :
    K0B.classify m m' (K0.of (gelem (eB_mem m m') (eB_idem m m') k)) = T k :=
  K0.cornerClassify_gelem _ _ _ _ _ _ k

/-- The shift of `E^{(a)} ⊠ E^{(b)} = B(e_a ⊗ e_b){C(a,2) + C(b,2)}`. -/
abbrev boxShift (m m' : ℕ) : ℤ := (((m+2).choose 2 : ℕ) : ℤ) + (((m'+2).choose 2 : ℕ) : ℤ)

theorem boxE_equiv : boxE m m' ≈ gelem (eB_mem m m') (eB_idem m m') (boxShift m m') :=
  (pairB m m').ind_gelem (projector_mem m) projector_mul_projector (projector_mem m')
    projector_mul_projector (eB_mem m m') (eB_idem m m') rfl rfl

theorem K0B.classify_boxE : K0B.classify m m' (K0.of (boxE m m')) = T (boxShift m m') := by
  rw [K0.of_eq (boxE_equiv m m'), K0B.classify_gelem]

/-- `[E^{(a)} ⊠ E^{(b)}]` is a `ℤ[q,q⁻¹]`-basis of `K₀(ONH_a ⊗ ONH_b)`. -/
def K0B.basis : Basis (Fin 1) (LaurentPolynomial ℤ) (K0 (gradB m m')) :=
  ((Basis.singleton (Fin 1) (LaurentPolynomial ℤ)).map (K0B.classify m m').symm).unitsSMul
    fun _ => (isUnit_T (boxShift m m')).unit

theorem K0B.basis_apply (i : Fin 1) : K0B.basis m m' i = K0.of (boxE m m') := by
  rw [K0B.basis, Basis.unitsSMul_apply, Basis.map_apply, Basis.singleton_apply, Units.smul_def,
    IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_eq,
    K0B.classify_boxE]

end Classify

end OddMath.Frontier.OddBialgebra
