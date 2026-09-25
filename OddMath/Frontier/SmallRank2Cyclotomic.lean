import OddMath.Frontier.SmallRankCyclotomic
import OddMath.Frontier.SmallRankLimit
import OddMath.Frontier.OddGrassmannSchur

/-!
# Ranks `0` and `1`, continued: gradings, graded Prop 5.2, (5.5)–(5.7), Prop 5.4

EKL arXiv:1111.1320v1, §5, pp. 44–46, and §6, p. 47, completing `SmallRankCyclotomic`.

* Gradings on `OH_{0,N} ≅ ℤ` and `OH_{1,N} ≅ ℤ[x]/(x^N)`, transported from `ℤ` (degree `0`) and
  from `ONH_1^N` (`Cyclotomic.onh1Grading`, `x` of degree `2`) along `OH_zero_equiv`,
  `OH_one_equiv` (`ohZeroGrading`, `ohOneGrading`). Both are connected, "graded local" (p. 47)
  (`ohZeroConnected`; `ohOneConnected` for `N ≥ 1`), `OH_{1,N}` is a direct sum of its pieces
  (`ohOneDecomposition`), and `K₀(OH_{a,N}) ≅ ℤ[q,q⁻¹]` (`ohZeroK0Equiv`, `ohOneK0Equiv`).
* **Prop 5.2, graded**, `a ≤ 1` (`prop_5_2_zero_degree_iff`, `prop_5_2_one_degree_iff`): the
  shifts `2ℓ(w) - 2ℓ(v)` vanish since `S_a` is trivial. For `a ≥ 2` see
  `Cyclotomic.prop_5_2_degree_iff`.
* **(5.5)–(5.7)** in every rank `a` (`supercentral_inverse_all`,
  `supercentral_inverse_unique_all`, `span_grassRelations`); for `a ≥ 2` see
  `Cyclotomic.supercentral_inverse`, `Cyclotomic.span_grassmannRelations`.
* **Prop 5.4**, vanishing part, in every rank `a` (`toOHQAll_sK_eq_zero`): `s_λ ↦ 0` in `OH_{a,a+b}`
  unless `λ ⊆ a × b`. For `a ≥ 2` see `OddGrassmannSchur.toOHQ_sK_eq_zero`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open FiniteCompleteElementary GradedK0 OddCategorification
open EKRadicalQuotient (Q)
open OddLREKIdentification (piN sK)
open scoped BigOperators

set_option synthInstance.maxHeartbeats 200000

noncomputable section

/-! ## Gradings on `OH_{0,N}` and `OH_{1,N}` -/

/-- The grading of `OH_{0,N} ≅ ℤ`, concentrated in degree `0`. -/
def ohZeroGrading (N : ℕ) : ℤ → AddSubgroup (OH 0 N) :=
  Cyclotomic.imageGrading (OH_zero_equiv N).symm.toRingHom intGrading

instance (N : ℕ) : SetLike.GradedMonoid (ohZeroGrading N) :=
  Cyclotomic.imageGrading.gradedMonoid _ _

/-- The grading of `OH_{1,N} ≅ ℤ[x]/(x^N)`, `x` of degree `2`. -/
def ohOneGrading (N : ℕ) : ℤ → AddSubgroup (OH 1 N) :=
  Cyclotomic.imageGrading (OH_one_equiv N).symm.toRingHom (Cyclotomic.onh1Grading N)

instance (N : ℕ) : SetLike.GradedMonoid (ohOneGrading N) :=
  Cyclotomic.imageGrading.gradedMonoid _ _

theorem mem_ohOneGrading_iff (N : ℕ) (d : ℤ) (x : OH 1 N) :
    x ∈ ohOneGrading N d ↔ OH_one_equiv N x ∈ Cyclotomic.onh1Grading N d := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change OH_one_equiv N ((OH_one_equiv N).symm y) ∈ _
    rwa [RingEquiv.apply_symm_apply]
  · intro h
    exact ⟨OH_one_equiv N x, h, (OH_one_equiv N).symm_apply_apply x⟩

theorem mem_ohZeroGrading_iff (N : ℕ) (d : ℤ) (x : OH 0 N) :
    x ∈ ohZeroGrading N d ↔ OH_zero_equiv N x ∈ intGrading d := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change OH_zero_equiv N ((OH_zero_equiv N).symm y) ∈ _
    rwa [RingEquiv.apply_symm_apply]
  · intro h
    exact ⟨OH_zero_equiv N x, h, (OH_zero_equiv N).symm_apply_apply x⟩

/-- `OH_{0,N}` is connected. -/
theorem ohZeroConnected (N : ℕ) : GradedK0.Connected (ohZeroGrading N) :=
  Cyclotomic.imageGrading_connected _ intConnected fun a b h => by
    have := congrArg (OH_zero_equiv N) h
    simpa only [map_intCast] using this

/-- `OH_{1,N}` is connected for `N ≥ 1` ("graded local", EKL p. 47). -/
theorem ohOneConnected {N : ℕ} (hN : 1 ≤ N) : GradedK0.Connected (ohOneGrading N) :=
  Cyclotomic.imageGrading_connected _ (Cyclotomic.onh1Connected hN) fun a b h => by
    have := congrArg (fun y => Cyclotomic.constONH1 hN (OH_one_equiv N y)) h
    simpa only [map_intCast] using this

/-- `OH_{1,N}` is the direct sum of its graded pieces. -/
theorem ohOneDecomposition (N : ℕ) : Cyclotomic.UniqueDecomposition (ohOneGrading N) :=
  Cyclotomic.UniqueDecomposition.image (Cyclotomic.onh1Decomposition N) _
    (OH_one_equiv N).symm.surjective (G := ∅) (by simp) fun x => by
      have hbot : TwoSidedIdeal.span (∅ : Set (Cyclotomic.ONH1 N)) = ⊥ :=
        le_bot_iff.mp (TwoSidedIdeal.span_le.mpr (Set.empty_subset _))
      rw [hbot, TwoSidedIdeal.mem_bot]
      exact (OH_one_equiv N).symm.map_eq_zero_iff

/-- `K₀(OH_{0,N}) ≅ ℤ[q,q⁻¹]`. -/
def ohZeroK0Equiv (N : ℕ) : K0 (ohZeroGrading N) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  K0.classify (ohZeroConnected N)

/-- `K₀(OH_{1,N}) ≅ ℤ[q,q⁻¹]` for `N ≥ 1`. -/
def ohOneK0Equiv {N : ℕ} (hN : 1 ≤ N) :
    K0 (ohOneGrading N) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  K0.classify (ohOneConnected hN)

/-! ## Prop 5.2, graded, for `a ≤ 1` -/

/-- **EKL Prop 5.2**, graded, `a = 0`: `x ∈ ONH_0^N = ℤ` has degree `d` iff the entry of the
`1 × 1` matrix has degree `d` (the shifts `2ℓ(w) - 2ℓ(v)` vanish). -/
theorem prop_5_2_zero_degree_iff (N : ℕ) (d : ℤ) (x : ℤ) :
    x ∈ intGrading d ↔ ∀ v w : Fin 1, prop_5_2_zero N x v w ∈ ohZeroGrading N d := by
  constructor
  · intro h v w
    exact ⟨x, h, rfl⟩
  · intro h
    have := (mem_ohZeroGrading_iff N d _).mp (h 0 0)
    change OH_zero_equiv N ((OH_zero_equiv N).symm x) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

/-- **EKL Prop 5.2**, graded, `a = 1`: `x ∈ ONH_1^N` has degree `d` iff the entry of the `1 × 1`
matrix has degree `d` (the shifts `2ℓ(w) - 2ℓ(v)` vanish). For `a ≥ 2` see
`Cyclotomic.prop_5_2_degree_iff`. -/
theorem prop_5_2_one_degree_iff (N : ℕ) (d : ℤ) (x : Cyclotomic.ONH1 N) :
    x ∈ Cyclotomic.onh1Grading N d ↔ ∀ v w : Fin 1, prop_5_2_one N x v w ∈ ohOneGrading N d := by
  constructor
  · intro h v w
    exact ⟨x, h, rfl⟩
  · intro h
    have := (mem_ohOneGrading_iff N d _).mp (h 0 0)
    change OH_one_equiv N ((OH_one_equiv N).symm x) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

/-! ## (5.5)–(5.7) in every rank -/

/-- `z_k = (-1)^{C(k+1,2)} h_k ∈ OΛ_a`, EKL (5.7), every rank. -/
def zAll (a k : ℕ) : OLam a := (-1 : ℤ)^((k+1).choose 2) • hAll a k

@[simp] theorem zAll_zero (a : ℕ) : zAll a 0 = 1 := by simp [zAll]

theorem eAll_zero (a : ℕ) : eAll a 0 = 1 := Subtype.ext (elementaryPoly_zero a)

theorem eAll_eq_zero {a k : ℕ} (hk : a < k) : eAll a k = 0 :=
  Subtype.ext (elementaryPoly_eq_zero_of_lt hk)

/-- **EKL (5.5)**, coefficient of `t^m` (`m ≥ 1`), every rank:
`Σ_k (-1)^{k(m-k)} ε_k z_{m-k} = 0`. -/
theorem supercentral_inverse_all (a m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^(k*(m-k)) • (eAll a k * zAll a (m-k)) = 0 := by
  apply Subtype.ext
  have h := elementary_complete_inverse a m hm
  have h2 := congrArg (fun p => (-1 : ℤ)^((m+1).choose 2) • p) h
  simp only [smul_zero, Finset.smul_sum, smul_smul] at h2
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Subring.coe_mul, zAll,
    ZeroMemClass.coe_zero, mul_smul_comm, smul_smul]
  rw [← h2]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [Nat.add_sub_cancel_left, Cyclotomic.sign_identity]
  rfl

/-- **EKL (5.5)**, converse, every rank: `z_k` is the unique solution with `z_0 = 1`. -/
theorem supercentral_inverse_unique_all (a : ℕ) (z : ℕ → OLam a) (h0 : z 0 = 1)
    (hz : ∀ m, 0 < m →
      ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^(k*(m-k)) • (eAll a k * z (m-k)) = 0) :
    z = zAll a := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [h0, zAll_zero]
    have h1 := hz m hm
    have h2 := supercentral_inverse_all a m hm
    rw [Finset.sum_range_succ'] at h1 h2
    have hs : ∑ k ∈ Finset.range m, (-1 : ℤ)^((k+1)*(m-(k+1))) • (eAll a (k+1) * z (m-(k+1))) =
        ∑ k ∈ Finset.range m, (-1 : ℤ)^((k+1)*(m-(k+1))) • (eAll a (k+1) * zAll a (m-(k+1))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih (m-(k+1)) (by have := Finset.mem_range.mp hk; omega)]
    simp only [Nat.zero_mul, pow_zero, one_smul, eAll_zero, one_mul, Nat.sub_zero] at h1 h2
    rw [hs] at h1
    exact add_left_cancel (h1.trans h2.symm)

/-- The coefficient of `t^m` in the truncated product (5.6)
`(1 + ε_1 t + ⋯ + ε_a t^a)(1 + z_1 t + ⋯ + z_{N-a} t^{N-a})`, every rank. -/
def grassRelation (a N m : ℕ) : OLam a :=
  ∑ k ∈ Finset.range (m+1),
    if k ≤ a ∧ m - k ≤ N - a then (-1 : ℤ)^(k*(m-k)) • (eAll a k * zAll a (m-k)) else 0

theorem zAll_mem (a N m : ℕ) (hm : N < m + a) : zAll a m ∈ grassIdeal a N :=
  TwoSidedIdeal.zsmul_mem _ _ (TwoSidedIdeal.subset_span ⟨m, hm, rfl⟩)

theorem grassRelation_eq (a N m : ℕ) (hm : 0 < m) :
    grassRelation a N m = -∑ k ∈ Finset.range (m+1),
      if k ≤ a ∧ m - k ≤ N - a then 0 else (-1 : ℤ)^(k*(m-k)) • (eAll a k * zAll a (m-k)) := by
  rw [eq_neg_iff_add_eq_zero, grassRelation, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl ?_).trans (supercentral_inverse_all a m hm)
  intro k _
  split_ifs <;> simp

theorem grassRelation_mem (a N m : ℕ) (hN : a ≤ N) (hm : 0 < m) :
    grassRelation a N m ∈ grassIdeal a N := by
  rw [grassRelation_eq a N m hm]
  apply TwoSidedIdeal.neg_mem
  refine sum_mem (fun k _ => ?_)
  split_ifs with h
  · exact TwoSidedIdeal.zero_mem _
  · rw [not_and_or] at h
    rcases h with h | h
    · rw [eAll_eq_zero (by omega), zero_mul, smul_zero]; exact TwoSidedIdeal.zero_mem _
    · exact TwoSidedIdeal.zsmul_mem _ _
        (TwoSidedIdeal.mul_mem_left _ _ _ (zAll_mem a N _ (by omega)))

/-- The relations of (5.6), all powers `t^m` with `m ≥ 1`. -/
def grassRelations (a N : ℕ) : Set (OLam a) := {x | ∃ m, 0 < m ∧ grassRelation a N m = x}

/-- **EKL (5.6)–(5.7)**, every rank: the coefficients of (5.6) generate `⟨h_m : m > N − a⟩`,
for `a ≤ N`. -/
theorem span_grassRelations (a N : ℕ) (hN : a ≤ N) :
    TwoSidedIdeal.span (grassRelations a N) = grassIdeal a N := by
  apply le_antisymm
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact grassRelation_mem a N m hN hm
  · rw [grassIdeal, TwoSidedIdeal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    set J := TwoSidedIdeal.span (grassRelations a N)
    suffices hz : ∀ m, N < m + a → zAll a m ∈ J by
      have h := TwoSidedIdeal.zsmul_mem J ((-1 : ℤ)^((m+1).choose 2)) (hz m hm)
      rwa [zAll, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul] at h
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hm0 : 0 < m := by omega
      have hR : grassRelation a N m ∈ J := TwoSidedIdeal.subset_span ⟨m, hm0, rfl⟩
      rw [grassRelation_eq a N m hm0, Finset.sum_range_succ'] at hR
      have hc : ¬ (0 ≤ a ∧ m - 0 ≤ N - a) := by omega
      simp only [hc, if_false, Nat.zero_mul, pow_zero, one_smul, eAll_zero, one_mul,
        Nat.sub_zero] at hR
      have hrest : (∑ k ∈ Finset.range m, if k+1 ≤ a ∧ m - (k+1) ≤ N - a then 0 else
          (-1 : ℤ)^((k+1)*(m-(k+1))) • (eAll a (k+1) * zAll a (m-(k+1)))) ∈ J := by
        refine sum_mem (fun k hk => ?_)
        have hk' := Finset.mem_range.mp hk
        split_ifs with h
        · exact TwoSidedIdeal.zero_mem _
        · rw [not_and_or] at h
          rcases h with h | h
          · rw [eAll_eq_zero (by omega), zero_mul, smul_zero]; exact TwoSidedIdeal.zero_mem _
          · exact TwoSidedIdeal.zsmul_mem _ _
              (TwoSidedIdeal.mul_mem_left _ _ _ (ih _ (by omega) (by omega)))
      have hmN : ¬ m ≤ N - a := by omega
      have := TwoSidedIdeal.sub_mem J (TwoSidedIdeal.neg_mem J hR) hrest
      simpa [hmN] using this

/-! ## Prop 5.4, vanishing part, in every rank -/

/-- `OΛ → OΛ_a → OH_{a,a+b}`, every rank. -/
def toOHQAll (a b : ℕ) : Q →+* OH a (a+b) := (toOH a (a+b)).comp (piAll a)

theorem piAll_h (a m : ℕ) : piAll a (EKElementaryQuotient.h m) = hAll a m :=
  Subtype.ext (OddLREKIdentification.piN_h _ _)

/-- **EKL Prop 5.4**, vanishing part, every rank: `s_λ ↦ 0` in `OH_{a,a+b}` unless
`λ ⊆ a × b`. For `a ≥ 2` see `OddGrassmannSchur.toOHQ_sK_eq_zero`. -/
theorem toOHQAll_sK_eq_zero (a b : ℕ) (lam : YoungDiagram)
    (h : OddGrassmannSchur.Outside a b lam) : toOHQAll a b (sK lam) = 0 := by
  have hmem : sK lam ∈ OddGrassmannSchur.boxIdeal a b :=
    (OddGrassmannSchur.mem_boxIdeal_iff a b _).mpr (Submodule.subset_span ⟨lam, h, rfl⟩)
  have hle : OddGrassmannSchur.boxIdeal a b ≤ TwoSidedIdeal.ker (toOHQAll a b) := by
    apply sup_le
    · intro y hy
      rw [TwoSidedIdeal.mem_ker, toOHQAll, RingHom.comp_apply, (piAll_eq_zero_iff a y).mpr hy,
        map_zero]
    · apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, toOHQAll, RingHom.comp_apply, piAll_h]
      exact toOH_hAll (by omega)
  exact (TwoSidedIdeal.mem_ker _).mp (hle hmem)

end

end OddMath.Frontier.SmallRank
