import OddMath.Frontier.OddBialgebraSmallFree

/-!
# `K₀(B) ≅ ℤ[q,q⁻¹]` and exact restriction for window data

EKL arXiv:1111.1320v1, §6, pp. 46–47. For window data `D` (`R₁ ⊗ R₂ ≅ B ⊂ ONH_{n+2}`) and
factor data `F₁`, `F₂` (`FactorCorner`: an idempotent `e ∈ R_0` with a splitting
`1 = ∑ σᵢ λᵢ`, `λᵢ σⱼ = δᵢⱼ e`, whose corner `e R e` vanishes in negative degrees and is `ℤ e` in
degree `0`):

* `splitS`: the tensor product splitting of `1 ∈ B` through `ẽ = e₁ ⊗ e₂`, with the Koszul sign;
* `cornerCondS_sandwich`, `cornerS_connected`: the corner `ẽ B ẽ` is connected;
* `K0S.classify : K₀(B) ≃ ℤ[q,q⁻¹]`, `[B ẽ{k}] ↦ q^k`;
* `res_exact`: `Res [E^{(n+2)}] = q^{-c} [E₁ ⊠ E₂]` whenever `[Rᵢ] = fᵢ [Eᵢ]` and
  `∑_u q^{-2ℓ(u)} f₁ f₂ = q^{-c} [n+2]!` (`u` over the shuffles).
-/

noncomputable section
open scoped TensorProduct
open LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords NilHeckeAction NilHeckeBasis GradedK0 OddCategorification QuantumSl2Plus

local notation "L" => LaurentPolynomial ℤ

/-- An idempotent `e ∈ R_0` with a splitting of `1` through `e` and a connected corner. -/
structure FactorCorner {R : Type*} [Ring R] (A : ℤ → AddSubgroup R) where
  /-- The idempotent. -/
  e : R
  idem : e * e = e
  mem : e ∈ A 0
  /-- The index set of the splitting. -/
  I : Type
  [fin : Fintype I]
  [dec : DecidableEq I]
  /-- The splitting `1 = ∑ σᵢ λᵢ`. -/
  S : Categorification.Splitting (1 : R) e I
  /-- Half-degrees of the `σᵢ`. -/
  k : I → ℤ
  sig : ∀ i, S.σ i ∈ A (2 * k i)
  lam : ∀ i, S.lam i ∈ A (2 * -k i)
  neg : ∀ {d : ℤ} {y : R}, y ∈ A d → d < 0 → e * y * e = 0
  zero : ∀ {y : R}, y ∈ A 0 → ∃ z : ℤ, e * y * e = z • e

attribute [instance] FactorCorner.fin FactorCorner.dec

namespace WinData

variable {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] {A₁ : ℤ → AddSubgroup R₁}
  {A₂ : ℤ → AddSubgroup R₂} {n p : ℕ} (D : WinData A₁ A₂ n p) (F₁ : FactorCorner A₁)
  (F₂ : FactorCorner A₂)

/-- `ẽ = e₁ ⊗ e₂ ∈ B`. -/
def eS : D.Bsub := D.pairS.ι₁ F₁.e * D.pairS.ι₂ F₂.e

theorem mem_zero₁ : F₁.e ∈ A₁ (2 * 0) := mem_of_deg_eq F₁.mem (by ring)

theorem mem_zero₂ : F₂.e ∈ A₂ (2 * 0) := mem_of_deg_eq F₂.mem (by ring)

theorem eS_idem : IsIdempotentElem (D.eS F₁ F₂) := by
  show D.pairS.ι₁ F₁.e * D.pairS.ι₂ F₂.e * (D.pairS.ι₁ F₁.e * D.pairS.ι₂ F₂.e) = _
  rw [mul_assoc, ← mul_assoc (D.pairS.ι₂ _), D.pairS.comm_zero_left F₁.mem (mem_zero₂ F₂),
    mul_assoc, ← mul_assoc (D.pairS.ι₁ _), ← map_mul, ← map_mul, F₁.idem, F₂.idem]
  rfl

theorem eS_mem : D.eS F₁ F₂ ∈ D.gradS 0 :=
  mem_of_deg_eq (SetLike.GradedMul.mul_mem (D.pairS.map₁ F₁.mem) (D.pairS.map₂ F₂.mem))
    (by ring)

instance : Fact (D.eS F₁ F₂ ∈ D.gradS 0) := ⟨D.eS_mem F₁ F₂⟩

/-- The degree of `σ̃_{(i,j)}`. -/
def dS (x : F₁.I × F₂.I) : ℤ := 2 * F₁.k x.1 + 2 * F₂.k x.2

/-- The tensor product splitting `1 = ∑ σ̃ λ̃` of `B` through `ẽ`. -/
def splitS : Categorification.Splitting (1 : D.Bsub) (D.eS F₁ F₂) (F₁.I × F₂.I) where
  σ x := D.pairS.ι₁ (F₁.S.σ x.1) * D.pairS.ι₂ (F₂.S.σ x.2)
  lam x := (F₁.k x.1 * F₂.k x.2).negOnePow •
    (D.pairS.ι₁ (F₁.S.lam x.1) * D.pairS.ι₂ (F₂.S.lam x.2))
  sum_eq := by
    have hterm : ∀ x : F₁.I × F₂.I,
        D.pairS.ι₁ (F₁.S.σ x.1) * D.pairS.ι₂ (F₂.S.σ x.2) *
          ((F₁.k x.1 * F₂.k x.2).negOnePow •
            (D.pairS.ι₁ (F₁.S.lam x.1) * D.pairS.ι₂ (F₂.S.lam x.2))) =
        D.pairS.ι₁ (F₁.S.σ x.1 * F₁.S.lam x.1) * D.pairS.ι₂ (F₂.S.σ x.2 * F₂.S.lam x.2) := by
      intro x
      rw [mul_smul_comm, mul_assoc, ← mul_assoc (D.pairS.ι₂ _),
        D.pairS.comm (F₁.lam x.1) (F₂.sig x.2), smul_mul_assoc, mul_smul_comm, smul_smul,
        ← Int.negOnePow_add, show F₁.k x.1 * F₂.k x.2 + -F₁.k x.1 * F₂.k x.2 = 0 by ring,
        Int.negOnePow_zero, one_smul, map_mul, map_mul]
      simp only [mul_assoc]
    simp only [hterm]
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum, F₁.S.sum_eq, F₂.S.sum_eq, map_one, map_one,
      one_mul]
  orth x y := by
    have e : ∀ (a b : R₁) (c d : R₂),
        D.pairS.ι₁ a * (D.pairS.ι₁ b * D.pairS.ι₂ c * D.pairS.ι₂ d) =
          D.pairS.ι₁ (a * b) * D.pairS.ι₂ (c * d) := fun a b c d => by
      rw [map_mul, map_mul]; simp only [mul_assoc]
    rw [smul_mul_assoc, mul_assoc, ← mul_assoc (D.pairS.ι₂ _),
      D.pairS.comm (F₁.sig y.1) (F₂.lam x.2), smul_mul_assoc, mul_smul_comm, smul_smul,
      ← mul_assoc, mul_assoc (D.pairS.ι₁ _), e, F₁.S.orth, F₂.S.orth]
    by_cases h1 : x.1 = y.1
    · by_cases h2 : x.2 = y.2
      · have hxy : x = y := Prod.ext h1 h2
        subst hxy
        rw [if_pos rfl, if_pos rfl, if_pos rfl, ← Int.negOnePow_add,
          show F₁.k x.1 * F₂.k x.2 + F₁.k x.1 * -F₂.k x.2 = 0 by ring, Int.negOnePow_zero,
          one_smul]
        rfl
      · rw [if_neg h2, map_zero, mul_zero, smul_zero, if_neg (fun h => h2 (congrArg Prod.snd h))]
    · rw [if_neg h1, map_zero, zero_mul, smul_zero, if_neg (fun h => h1 (congrArg Prod.fst h))]
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

theorem splitS_sigma_mem (x : F₁.I × F₂.I) : (D.splitS F₁ F₂).σ x ∈ D.gradS (dS F₁ F₂ x) :=
  SetLike.GradedMul.mul_mem (D.pairS.map₁ (F₁.sig x.1)) (D.pairS.map₂ (F₂.sig x.2))

theorem splitS_lam_mem (x : F₁.I × F₂.I) : (D.splitS F₁ F₂).lam x ∈ D.gradS (-dS F₁ F₂ x) :=
  units_smul_mem _ (mem_of_deg_eq (SetLike.GradedMul.mul_mem (D.pairS.map₁ (F₁.lam x.1))
    (D.pairS.map₂ (F₂.lam x.2))) (by simp only [dS]; ring))

/-! ### The corner `ẽ B ẽ` is connected -/

/-- Degree-`d` condition on a corner element. -/
def CornerCondS (d : ℤ) (v : D.Bsub) : Prop :=
  (d < 0 → v = 0) ∧ (d = 0 → ∃ z : ℤ, v = z • D.eS F₁ F₂)

theorem CornerCondS.zero (d : ℤ) : D.CornerCondS F₁ F₂ d 0 :=
  ⟨fun _ => rfl, fun _ => ⟨0, by rw [zero_smul]⟩⟩

theorem CornerCondS.add {d : ℤ} {v w : D.Bsub} (hv : D.CornerCondS F₁ F₂ d v)
    (hw : D.CornerCondS F₁ F₂ d w) : D.CornerCondS F₁ F₂ d (v + w) := by
  refine ⟨fun hd => by rw [hv.1 hd, hw.1 hd, add_zero], fun hd => ?_⟩
  obtain ⟨z, hz⟩ := hv.2 hd
  obtain ⟨z', hz'⟩ := hw.2 hd
  exact ⟨z + z', by rw [hz, hz', add_smul]⟩

theorem CornerCondS.smul {d : ℤ} {v : D.Bsub} (hv : D.CornerCondS F₁ F₂ d v) (c : ℤ) :
    D.CornerCondS F₁ F₂ d (c • v) := by
  refine ⟨fun hd => by rw [hv.1 hd, smul_zero], fun hd => ?_⟩
  obtain ⟨z, hz⟩ := hv.2 hd
  exact ⟨c * z, by rw [hz, smul_smul]⟩

theorem eS_sandwich_tensor {i j : ℤ} {x : R₁} {x' : R₂} (hx : x ∈ A₁ (2 * i))
    (hx' : x' ∈ A₂ (2 * j)) :
    D.eS F₁ F₂ * (D.pairS.ι₁ x * D.pairS.ι₂ x') * D.eS F₁ F₂ =
      D.pairS.ι₁ (F₁.e * x * F₁.e) * D.pairS.ι₂ (F₂.e * x' * F₂.e) := by
  have h1 := D.pairS.comm_zero_right hx F₂.mem
  have h2 := D.pairS.comm_zero_left F₁.mem hx'
  have h3 := D.pairS.comm_zero_left F₁.mem (mem_zero₂ F₂)
  simp only [eS, map_mul, mul_assoc]
  rw [comm_assoc h1, comm_assoc h2, comm_assoc h3]

theorem cornerCondS_tensor {i j : ℤ} {x : R₁} {x' : R₂} (hx : x ∈ A₁ (2 * i))
    (hx' : x' ∈ A₂ (2 * j)) :
    D.CornerCondS F₁ F₂ (2 * i + 2 * j)
      (D.eS F₁ F₂ * (D.pairS.ι₁ x * D.pairS.ι₂ x') * D.eS F₁ F₂) := by
  rw [D.eS_sandwich_tensor F₁ F₂ hx hx']
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rcases lt_or_le (2 * i) 0 with h | h
    · rw [F₁.neg hx h, map_zero, zero_mul]
    · rw [F₂.neg hx' (by omega), map_zero, mul_zero]
  · rcases lt_trichotomy (2 * i) 0 with h | h | h
    · exact ⟨0, by rw [F₁.neg hx h, map_zero, zero_mul, zero_smul]⟩
    · obtain ⟨z, hz⟩ := F₁.zero (h ▸ hx)
      obtain ⟨z', hz'⟩ := F₂.zero
        (show x' ∈ A₂ 0 by rw [show (0 : ℤ) = 2 * j by omega]; exact hx')
      refine ⟨z * z', ?_⟩
      rw [hz, hz', map_zsmul, map_zsmul, smul_mul_smul_comm]
      rfl
    · exact ⟨0, by rw [F₂.neg hx' (by omega), map_zero, mul_zero, zero_smul]⟩

theorem repr_tmap_bT (ij kl : D.I₁ × D.I₂) (hne : kl ≠ ij) :
    (basis n).repr (D.tmap (D.bT kl)) (D.φ ij) = 0 := by
  have hφ : D.φ kl ≠ D.φ ij := fun h => hne (D.inj h)
  rw [tmap_bT]
  rcases D.sign kl.1 kl.2 with h | h <;> rw [h]
  · rw [Basis.repr_self, Finsupp.single_eq_of_ne hφ]
  · rw [map_neg, Basis.repr_self, Finsupp.neg_apply, Finsupp.single_eq_of_ne hφ, neg_zero]

theorem repr_tmap_bT_self (ij : D.I₁ × D.I₂) :
    (basis n).repr (D.tmap (D.bT ij)) (D.φ ij) ≠ 0 := by
  rw [tmap_bT]
  rcases D.sign ij.1 ij.2 with h | h <;> rw [h]
  · rw [Basis.repr_self, Finsupp.single_eq_same]; exact one_ne_zero
  · rw [map_neg, Basis.repr_self, Finsupp.neg_apply, Finsupp.single_eq_same]
    exact neg_ne_zero.2 one_ne_zero

/-- **The corner `ẽ B ẽ` vanishes in negative degrees and is `ℤ ẽ` in degree `0`.** -/
theorem cornerCondS_sandwich {d : ℤ} {y : D.Bsub} (hy : y ∈ D.gradS d) :
    D.CornerCondS F₁ F₂ d (D.eS F₁ F₂ * y * D.eS F₁ F₂) := by
  obtain ⟨t, ht⟩ := y.2
  set c := D.bT.repr t
  have ht' : (y : Presented n) = ∑ q ∈ c.support, c q • D.tmap (D.bT q) := by
    rw [← ht]
    conv_lhs => rw [← D.bT.linearCombination_repr t]
    rw [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_zsmul]
  have hy' : y = ∑ q ∈ c.support,
      c q • (D.pairS.ι₁ (D.b₁ q.1) * D.pairS.ι₂ (D.b₂ q.2)) := by
    apply Subtype.ext
    rw [ht']
    push_cast
    simp only [pairS_ι₁, pairS_ι₂, tmap_bT]
  have hw : ∀ q ∈ c.support, 2 * D.wt₁ q.1 + 2 * D.wt₂ q.2 = d := by
    intro q hq
    rw [← D.weight q]
    have hsupp := (Basis.mem_span_image (basis n)).1
      (mem_span_weight (show (y : Presented n) ∈ onhGrading n d from hy))
    refine hsupp (Finsupp.mem_support_iff.2 ?_)
    rw [ht', map_sum, Finsupp.finset_sum_apply]
    simp only [map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single q (fun k _ hk => by rw [D.repr_tmap_bT q k hk, mul_zero])
      (fun h => absurd hq h)]
    exact mul_ne_zero (Finsupp.mem_support_iff.1 hq) (D.repr_tmap_bT_self q)
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_induction _ (D.CornerCondS F₁ F₂ d) (fun _ _ => CornerCondS.add D F₁ F₂)
    (CornerCondS.zero D F₁ F₂ d) fun q hq => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  refine CornerCondS.smul D F₁ F₂ ?_ _
  have := D.cornerCondS_tensor F₁ F₂ (D.mem₁ q.1) (D.mem₂ q.2)
  rwa [hw q hq] at this

theorem eS_ne_zero_of (h : (D.eS F₁ F₂ : Presented n) ≠ 0) {z w : ℤ}
    (hzw : z • D.eS F₁ F₂ = w • D.eS F₁ F₂) : z = w := by
  have h' : z • (D.eS F₁ F₂ : Presented n) = w • (D.eS F₁ F₂ : Presented n) :=
    congrArg Subtype.val hzw
  rw [← sub_eq_zero, ← sub_smul, (basis n).smul_eq_zero] at h'
  rcases h' with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' h

/-- **The corner `ẽ B ẽ` is connected** (given `ẽ ≠ 0`). -/
theorem cornerS_connected (hne : (D.eS F₁ F₂ : Presented n) ≠ 0) :
    Connected (cornerGrading D.gradS (D.eS_idem F₁ F₂)) where
  neg d hd x hx := by
    have h := (D.cornerCondS_sandwich F₁ F₂ hx).1 hd
    rw [mul_assoc, cval_apply, corner_right, corner_left] at h
    exact Subtype.ext h
  zero x hx := by
    obtain ⟨z, hz⟩ := (D.cornerCondS_sandwich F₁ F₂ hx).2 rfl
    rw [mul_assoc, cval_apply, corner_right, corner_left] at hz
    refine ⟨z, Subtype.ext ?_⟩
    rw [hz, ← zsmul_one, ← cval_apply, map_zsmul]
    rfl
  inj z w h := by
    have h' := congrArg (cval (D.eS_idem F₁ F₂)) h
    rw [← zsmul_one, ← zsmul_one w, map_zsmul, map_zsmul] at h'
    exact D.eS_ne_zero_of F₁ F₂ hne h'

/-- `K₀(B) ≅ ℤ[q,q⁻¹]`, `[B ẽ{k}] ↦ q^k`. -/
def K0S.classify (hne : (D.eS F₁ F₂ : Presented n) ≠ 0) :
    K0 D.gradS ≃ₗ[L] L :=
  K0.cornerClassify (D.splitS F₁ F₂) (D.splitS_sigma_mem F₁ F₂) (D.splitS_lam_mem F₁ F₂)
    (D.cornerS_connected F₁ F₂ hne)

theorem K0S.classify_gelem (hne : (D.eS F₁ F₂ : Presented n) ≠ 0) (k : ℤ) :
    K0S.classify D F₁ F₂ hne (K0.of (gelem (D.eS_mem F₁ F₂) (D.eS_idem F₁ F₂) k)) = T k :=
  K0.cornerClassify_gelem _ _ _ _ _ _ k

/-! ### Exact restriction -/

/-- `E₁ ⊠ E₂ = B (e₁ ⊗ e₂){c₁ + c₂}`. -/
def boxS (c₁ c₂ : ℤ) : GIdem D.gradS := D.pairS.ind (gelem F₁.mem F₁.idem c₁)
  (gelem F₂.mem F₂.idem c₂)

theorem boxS_equiv (c₁ c₂ : ℤ) :
    D.boxS F₁ F₂ c₁ c₂ ≈ gelem (D.eS_mem F₁ F₂) (D.eS_idem F₁ F₂) (c₁ + c₂) :=
  D.pairS.ind_gelem F₁.mem F₁.idem F₂.mem F₂.idem (D.eS_mem F₁ F₂) (D.eS_idem F₁ F₂) rfl rfl

theorem K0S.classify_boxS (hne : (D.eS F₁ F₂ : Presented n) ≠ 0) (c₁ c₂ : ℤ) :
    K0S.classify D F₁ F₂ hne (K0.of (D.boxS F₁ F₂ c₁ c₂)) = T (c₁ + c₂) := by
  rw [K0.of_eq (D.boxS_equiv F₁ F₂ c₁ c₂), K0S.classify_gelem]

/-- `[B] = f₁ f₂ [E₁ ⊠ E₂]` when `[Rᵢ] = fᵢ [Eᵢ]`. -/
theorem class_Bsub [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] (c₁ c₂ : ℤ) (f₁ f₂ : L)
    (h₁ : K0.of (GIdem.single 0 : GIdem A₁) = f₁ • K0.of (gelem F₁.mem F₁.idem c₁))
    (h₂ : K0.of (GIdem.single 0 : GIdem A₂) = f₂ • K0.of (gelem F₂.mem F₂.idem c₂)) :
    K0.of (GIdem.single 0 : GIdem D.gradS) = (f₁ * f₂) • K0.of (D.boxS F₁ F₂ c₁ c₂) := by
  have h : K0.of (GIdem.single 0 : GIdem D.gradS) =
      D.pairS.indK0 (K0.of (GIdem.single 0)) (K0.of (GIdem.single 0)) :=
    (D.pairS.indK0_of_of _ _).trans (K0.of_eq (D.pairS.ind_gelem
      SetLike.GradedOne.one_mem (one_mul 1) SetLike.GradedOne.one_mem (one_mul 1)
      SetLike.GradedOne.one_mem (one_mul 1) (by rw [map_one, map_one, one_mul]) (add_zero 0)))
      |>.symm
  rw [h, h₁, h₂, map_smul, LinearMap.map_smul₂, smul_smul, SuperPair.indK0_of_of, boxS,
    mul_comm]

/-- **Exact restriction**: `Res [E^{(n+2)}] = q^{-c} [E₁ ⊠ E₂]`. -/
theorem res_exact [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂]
    (hne : (D.eS F₁ F₂ : Presented n) ≠ 0) (c₁ c₂ c : ℤ) (f₁ f₂ : L)
    (h₁ : K0.of (GIdem.single 0 : GIdem A₁) = f₁ • K0.of (gelem F₁.mem F₁.idem c₁))
    (h₂ : K0.of (GIdem.single 0 : GIdem A₂) = f₂ • K0.of (gelem F₂.mem F₂.idem c₂))
    (hsum : (∑ u : ShufT n p, (T (-(2 * (length u.1 : ℤ))) : L)) * (f₁ * f₂) =
      T (-c) * qFact (n+2)) :
    D.res (K0.of (divE n)) = (T (-c) : L) • K0.of (D.boxS F₁ F₂ c₁ c₂) := by
  have key : qFact (n+2) • (D.res (K0.of (divE n)) - (T (-c) : L) •
      K0.of (D.boxS F₁ F₂ c₁ c₂)) = 0 := by
    rw [smul_sub, ← map_smul, ← eq_6_1_qFact, res_one, ← Finset.sum_smul,
      D.class_Bsub F₁ F₂ c₁ c₂ f₁ f₂ h₁ h₂, smul_smul, smul_smul, hsum, sub_eq_zero, mul_comm]
  have h := congrArg (K0S.classify D F₁ F₂ hne) key
  rw [map_smul, map_zero, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (qFact_ne_zero _)
  · exact sub_eq_zero.1 ((K0S.classify D F₁ F₂ hne).injective (h.trans (map_zero _).symm))

end WinData

/-- `∑_{w ∈ S_{n+2}} q^{-2ℓ(w)}` factors over the Young subgroup and the shuffles. -/
theorem sum_length_young (n p : ℕ) :
    ∑ w : Perm n, (T (-(2 * (length w : ℤ))) : L) =
      (∑ y : YoungT n p, (T (-(2 * (length y.1 : ℤ))) : L)) *
        ∑ u : ShufT n p, (T (-(2 * (length u.1 : ℤ))) : L) := by
  rw [← Equiv.sum_comp (youngFactorEquiv (n := n) (p := p))
    (fun w => (T (-(2 * (length w : ℤ))) : L)), Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [youngFactorEquiv_apply, length_young_mul y.2 u.2, ← T_add]
  congr 1
  push_cast
  ring

end OddMath.Frontier.OddBialgebra
