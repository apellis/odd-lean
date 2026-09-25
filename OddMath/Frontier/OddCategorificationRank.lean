import OddMath.Frontier.OddCategorificationBasic
import OddMath.Frontier.NilHeckeGradedEnd
import OddMath.Frontier.ThickDecomposition

/-!
# `K₀` of the odd nilHecke rings `ONH_a`

EKL arXiv:1111.1320v1, §6, pp. 46–47. Gradings in the paper normalization: a dot has degree
`2`, a crossing degree `-2`, and `q = T 1` acts on `K₀` by the shift `{1}`.

* `onhGrading n`: the grading of `ONH_a = NilHeckeAction.Presented n` (`a = n+2`) by
  `NilHeckeGrading.degreePiece`; `kerGrading n`: the grading of `OΛ_a` (`K n`) by
  `kernelPiece`, which is connected (`kerConnected`).
* `onhIso n : ONH_a ≃+* Mat_{S_a}(OΛ_a)` (Corollary 2.14) is graded for `matGrading` with
  `d w = 2 ℓ(w)` (`mem_onhGrading_iff`, from `graded_matrix_corollary`); with graded Morita
  invariance and the classification over `OΛ_a`, `K₀(ONH_a) ≃ ℤ[q,q⁻¹]` (`onhK0Equiv`), and
  `[ONH_a] ↦ ∑_{w ∈ S_a} q^{-2ℓ(w)}` (`onhK0Equiv_one`).
* `ONH_0 = ℤ` (`intGrading`) and `ONH_1 = OPol_1 = SkewPolynomial 1` (`opolGrading`) are
  connected, so `K₀ ≃ ℤ[q,q⁻¹]` by `K0.classify`.
* Degrees in `degreePiece`: `e_a` has degree `0`, `σ_ℓ`, `λ_ℓ` of (6.1) have degrees
  `±2(|ℓ| - C(a,2))`, and `σ_α`, `λ_α` of (6.2) degrees `±2(|α| - ab)` (`mem_of_hasDegree`,
  from the degrees of the operators on `OPol_a`).
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddCategorification
open GradedK0 NilHeckeAction NilHeckeGrading NilHeckeGradedEnd NilHeckeEndomorphism
  NilCoxeterWords
open OddMath.SkewPolynomial (SkewPolynomial)

/-! ### Degree-zero polynomials -/

theorem pdegree_eq_zero {N : ℕ} {a : Fin N → ℕ} (h : pdegree a = 0) : a = 0 := by
  have hs : ∑ i, a i = 0 := by
    have : ((∑ i, a i : ℕ) : ℤ) = 0 := by simp only [pdegree] at h; omega
    exact_mod_cast this
  funext i
  exact (Finset.sum_eq_zero_iff.1 hs) i (Finset.mem_univ i)

theorem intCast_skew (N : ℕ) (z : ℤ) : ((z : ℤ) : SkewPolynomial N) = Finsupp.single 0 z := by
  show z • OddMath.SkewPolynomial.monomial (0 : Fin N → ℕ) 1 = _
  rw [OddMath.SkewPolynomial.monomial, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem eq_intCast_of_mem {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ polynomialPiece N 0) :
    f = ((f 0 : ℤ) : SkewPolynomial N) := by
  rw [intCast_skew]
  ext a
  by_cases ha : a = 0
  · subst ha
    rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm ha)]
    exact hf a fun h => ha (pdegree_eq_zero h)

theorem intCast_skew_injective (N : ℕ) : Function.Injective (Int.cast : ℤ → SkewPolynomial N) :=
  fun z w h => by
    have := congrArg (fun f : SkewPolynomial N => f 0) h
    simpa [intCast_skew] using this

/-! ### The gradings -/

/-- The grading of `ONH_a`, `a = n+2`: dots of degree `2`, crossings of degree `-2`. -/
def onhGrading (n : ℕ) (d : ℤ) : AddSubgroup (Presented n) := (degreePiece n d).toAddSubgroup

instance onhGrading.gradedMonoid (n : ℕ) : SetLike.GradedMonoid (onhGrading n) where
  one_mem := unit_mem
  mul_mem _ _ _ _ hx hy := degreePiece_mul hx hy

/-- The grading of `OΛ_a = K n` by polynomial degree. -/
def kerGrading (n : ℕ) (d : ℤ) : AddSubgroup (K n) := (kernelPiece n d).toAddSubgroup

instance kerGrading.gradedMonoid (n : ℕ) : SetLike.GradedMonoid (kerGrading n) where
  one_mem := NilHeckeGradedEnd.one_mem (n+2)
  mul_mem _ _ _ _ hx hy := polynomial_mul hx hy

theorem kerConnected (n : ℕ) : Connected (kerGrading n) where
  neg d hd x hx := by
    have hx' : x ∈ kernelPiece n d := hx
    rw [kernel_negative n d hd] at hx'
    exact (Submodule.mem_bot ℤ).1 hx'
  zero x hx := ⟨(x : SkewPolynomial (n+2)) 0, Subtype.ext (by
    rw [SubringClass.coe_intCast]
    exact (eq_intCast_of_mem hx).symm)⟩
  inj z w h := intCast_skew_injective (n+2) (by
    have := congrArg Subtype.val h
    rwa [SubringClass.coe_intCast, SubringClass.coe_intCast] at this)

/-- The grading of `ONH_1 = OPol_1 = SkewPolynomial 1`. -/
def opolGrading (d : ℤ) : AddSubgroup (SkewPolynomial 1) := (polynomialPiece 1 d).toAddSubgroup

instance opolGrading.gradedMonoid : SetLike.GradedMonoid opolGrading where
  one_mem := NilHeckeGradedEnd.one_mem 1
  mul_mem _ _ _ _ hx hy := polynomial_mul hx hy

theorem opolConnected : Connected opolGrading where
  neg d hd x hx := by
    have hx' : x ∈ polynomialPiece 1 d := hx
    rw [polynomial_negative 1 d hd] at hx'
    exact (Submodule.mem_bot ℤ).1 hx'
  zero x hx := ⟨x 0, (eq_intCast_of_mem hx).symm⟩
  inj := intCast_skew_injective 1

/-- The grading of `ONH_0 = ℤ`, concentrated in degree `0`. -/
def intGrading (d : ℤ) : AddSubgroup ℤ where
  carrier := {x | x = 0 ∨ d = 0}
  add_mem' {x y} hx hy := by
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, add_zero])
      · exact Or.inr hy
    · exact Or.inr hx
  zero_mem' := Or.inl rfl
  neg_mem' {x} hx := by
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx, neg_zero])
    · exact Or.inr hx

instance intGrading.gradedMonoid : SetLike.GradedMonoid intGrading where
  one_mem := Or.inr rfl
  mul_mem i j x y hx hy := by
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx, zero_mul])
    rcases hy with hy | hy
    · exact Or.inl (by rw [hy, mul_zero])
    · exact Or.inr (by rw [hx, hy, add_zero])

theorem intConnected : Connected intGrading where
  neg d hd x hx := hx.resolve_right (by omega)
  zero x _ := ⟨x, Int.cast_id⟩
  inj := fun _ _ h => by simpa using h

/-! ### `ONH_a` as a graded matrix ring over `OΛ_a` -/

/-- The shifts `d w = 2 ℓ(w)` of the Schubert basis. -/
def lenShift (n : ℕ) (w : Perm n) : ℤ := 2 * (length w : ℤ)

/-- Corollary 2.14: `ONH_a ≃ End_{OΛ_a}(OPol_a) ≃ Mat_{S_a}(OΛ_a)`. -/
def onhIso (n : ℕ) : Presented n ≃+* Matrix (Perm n) (Perm n) (K n) :=
  (actionEquiv n).trans (matrixEquiv n)

theorem mem_onhGrading_iff (n : ℕ) (d : ℤ) (x : Presented n) :
    x ∈ onhGrading n d ↔ onhIso n x ∈ matGrading (kerGrading n) (lenShift n) d := by
  show x ∈ degreePiece n d ↔ ∀ i j, _ ∈ kernelPiece n _
  rw [graded_matrix_corollary]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [lenShift, lenShift, show d - 2 * (length i : ℤ) + 2 * (length j : ℤ) =
    d + 2 * (length j : ℤ) - 2 * (length i : ℤ) by ring]
  rfl

/-- `K₀(ONH_a) ≃ ℤ[q,q⁻¹]` (`a = n+2`): the graded ring isomorphism `onhIso`, graded Morita
invariance, and the classification over the connected ring `OΛ_a`. -/
def onhK0Equiv (n : ℕ) : K0 (onhGrading n) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  (k0Equiv (onhIso n) (mem_onhGrading_iff n)).trans (K0.morita.trans (K0.classify (kerConnected n)))

/-- `[ONH_a] ↦ ∑_{w ∈ S_a} q^{-2ℓ(w)}`. -/
theorem onhK0Equiv_one (n : ℕ) :
    onhK0Equiv n (K0.of (GIdem.single 0)) = ∑ w : Perm n, T (-(2 * (length w : ℤ))) := by
  simp only [onhK0Equiv, LinearEquiv.trans_apply, k0Equiv_of, K0.morita_of, K0.classify_of]
  rw [← gdimAux_eq_of_mvn (kerConnected n) (GIdem.mvn_flatten _)]
  have h1 : (gmap (onhIso n) (mem_onhGrading_iff n) (GIdem.single 0)).e = 1 := by
    show (1 : Matrix (Fin 1) (Fin 1) (Presented n)).map (onhIso n) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : flat (gmap (onhIso n) (mem_onhGrading_iff n) (GIdem.single 0)).e = 1 := by
    rw [h1]
    exact (Matrix.compRingEquiv (Fin 1) (Perm n) (K n)).map_one
  rw [h2, gdimAux_one (kerConnected n), Fintype.sum_prod_type]
  erw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [gmap, GIdem.single, GIdem.free, lenShift]

/-! ### Degrees in `degreePiece` -/

section Degrees
open GradedTrace ProjectorRank

/-- An element acting on `OPol_a` with degree `k` (a dot of degree `1`) has degree `2k`. -/
theorem mem_of_hasDegree {n : ℕ} {x : Presented n} {k : ℤ}
    (h : HasDegree (Vd (n+2)) k (action n x)) : x ∈ onhGrading n (2 * k) := by
  show x ∈ degreePiece n (2 * k)
  rw [actionEquiv_degree_iff]
  intro e f hf
  rw [actionEquiv_apply]
  by_cases he : e % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m := ⟨e / 2, by omega⟩
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact h m f hf
  · rw [polynomial_odd _ _ he] at hf
    rw [(Submodule.mem_bot ℤ).1 hf, map_zero]
    exact zero_mem _

theorem projector_mem (n : ℕ) : ZeroHecke.projector n ∈ onhGrading n 0 := by
  simpa using mem_of_hasDegree (hasDegree_projector (n := n))

theorem blockE_pair_mem (n a b : ℕ) :
    ThickBubble.blockE n 0 a * ThickBubble.blockE n a b ∈ onhGrading n 0 := by
  have h := degreePiece_mul (mem_of_hasDegree (ThickDecomposition.hasDegree_blockE (n := n) 0 a))
    (mem_of_hasDegree (ThickDecomposition.hasDegree_blockE (n := n) a b))
  simpa using h

/-- `σ_ℓ` of (6.1) has degree `2(|ℓ| - C(a,2))`. -/
theorem sigma61_mem {n : ℕ} {ℓ : Fin (n+1) → ℕ} (hℓ : ∀ ν : Fin (n+1), ℓ ν ≤ ν.val + 1) :
    ThickMatrixUnits.sigma ℓ ∈ onhGrading n (2 * Categorification.deg61 ℓ) := by
  have h := mem_of_hasDegree (ThickMatrixUnits.hasDegree_sigma hℓ)
  rwa [ThickMatrixUnits.sigmaDeg_extend] at h

/-- `λ_ℓ` of (6.1) has degree `-2(|ℓ| - C(a,2))`. -/
theorem lam61_mem {n : ℕ} {ℓ : Fin (n+1) → ℕ} (hℓ : ∀ ν : Fin (n+1), ℓ ν ≤ ν.val + 1) :
    ThickMatrixUnits.lam ℓ ∈ onhGrading n (-(2 * Categorification.deg61 ℓ)) := by
  have h := mem_of_hasDegree (ThickMatrixUnits.hasDegree_lam hℓ)
  rw [ThickMatrixUnits.sigmaDeg_extend] at h
  exact mem_of_deg_eq h (by rw [Categorification.deg61]; ring)

/-- `σ_α` of (6.2) has degree `2(|α| - ab)`. -/
theorem sigma62_mem {n a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    ThickBubble.sigma n a b hab α ∈ onhGrading n (2 * ThickDecomposition.shift a b α) :=
  mem_of_hasDegree (ThickDecomposition.hasDegree_sigma hab α)

/-- `λ_α` of (6.2) has degree `-2(|α| - ab)`. -/
theorem lam62_mem {n a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} (hα : ∀ k, α k ≤ b) :
    ThickBubble.lam n a b hab α ∈ onhGrading n (-(2 * ThickDecomposition.shift a b α)) :=
  mem_of_deg_eq (mem_of_hasDegree (ThickDecomposition.hasDegree_lam hab hα)) (by ring)

end Degrees

/-! ### The Mahonian identity -/

section Mahonian
open BoxPartitionCount

theorem prod_geom_mul (a : ℕ) :
    (∏ j ∈ Finset.range a, ∑ k ∈ Finset.range (j+1), (PowerSeries.X : PowerSeries ℤ) ^ k) *
      (1 - PowerSeries.X) ^ a = qPoch a := by
  have h : (1 - PowerSeries.X : PowerSeries ℤ) ^ a =
      ∏ _j ∈ Finset.range a, (1 - PowerSeries.X) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [qPoch, h, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [geom_sum_mul_neg]

/-- `∑_{ℓ ∈ Sq(a)} X^{|ℓ|} = ∏_{j < a} (1 + X + ⋯ + X^j)`. -/
theorem sum_Sq_eq_prod (a : ℕ) :
    (∑ ℓ ∈ Sq a, Polynomial.X ^ (∑ ν, ℓ ν) : Polynomial ℤ) =
      ∏ j ∈ Finset.range a, ∑ k ∈ Finset.range (j+1), (Polynomial.X : Polynomial ℤ) ^ k := by
  rw [← Polynomial.coe_inj]
  have hX : (1 - PowerSeries.X : PowerSeries ℤ) ^ a ≠ 0 := by
    refine pow_ne_zero _ fun h => ?_
    have := congrArg (PowerSeries.constantCoeff ℤ) h
    simp at this
  refine mul_right_cancel₀ hX ?_
  have h1 : ((∑ ℓ ∈ Sq a, Polynomial.X ^ (∑ ν, ℓ ν) : Polynomial ℤ) : PowerSeries ℤ) =
      qfact a := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [qfact, Polynomial.coe_pow]
  have h2 : ((∏ j ∈ Finset.range a, ∑ k ∈ Finset.range (j+1),
      (Polynomial.X : Polynomial ℤ) ^ k : Polynomial ℤ) : PowerSeries ℤ) =
      ∏ j ∈ Finset.range a, ∑ k ∈ Finset.range (j+1), (PowerSeries.X : PowerSeries ℤ) ^ k := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp [map_sum, Polynomial.coe_pow]
  rw [h1, h2, qfact_mul, prod_geom_mul]

/-- Mahonian identity: `∑_{w ∈ S_a} X^{ℓ(w)} = ∑_{ℓ ∈ Sq(a)} X^{|ℓ|}` (both are the
`q`-factorial). -/
theorem sum_length_eq_sum_Sq (n : ℕ) :
    (∑ w : Perm n, Polynomial.X ^ length w : Polynomial ℤ) =
      ∑ ℓ ∈ Sq (n+2), Polynomial.X ^ (∑ ν, ℓ ν) := by
  rw [sum_Sq_eq_prod]
  exact schubert_rank_polynomial n

/-- `∑_{w ∈ S_a} q^{-2ℓ(w)} = ∑_{ℓ ∈ Sq(a)} q^{-2|ℓ|}` in `ℤ[q,q⁻¹]`. -/
theorem sum_T_length_eq (n : ℕ) :
    ∑ w : Perm n, (T (-(2 * (length w : ℤ))) : LaurentPolynomial ℤ) =
      ∑ ℓ : Sq (n+2), T (-(2 * ((∑ ν, ℓ.1 ν : ℕ) : ℤ))) := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ))
    (T (-2) : LaurentPolynomial ℤ)) (sum_length_eq_sum_Sq n)
  simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_X_pow, T_pow] at h
  rw [Finset.sum_coe_sort (Sq (n+2)) fun ℓ => (T (-(2 * ((∑ ν, ℓ ν : ℕ) : ℤ))) :
    LaurentPolynomial ℤ)]
  convert h using 2 with w _ ℓ _
  · congr 1; ring
  · congr 1; ring

/-- Augmentation `q ↦ 1`. -/
def augment : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) 1

@[simp] theorem augment_T (k : ℤ) : augment (T k) = 1 := by
  simp [augment]

theorem sum_T_Sq_ne_zero (n : ℕ) (c : Sq (n+2) → ℤ) :
    ∑ ℓ : Sq (n+2), (T (c ℓ) : LaurentPolynomial ℤ) ≠ 0 := by
  intro h
  have := congrArg augment h
  simp only [map_sum, augment_T, Finset.sum_const, Finset.card_univ, map_zero,
    Fintype.card_coe, card_Sq, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
  exact Nat.factorial_ne_zero _ this

end Mahonian

/-! ### (6.1) in `K₀` and the class of `E^{(a)}` -/

section Eq61
open ZeroHecke BoxPartitionCount

/-- `ONH_a` as the graded projective `ONH_a · 1`. -/
def onhFree (n : ℕ) : GIdem (onhGrading n) := gelem (A := onhGrading n) unit_mem (one_mul 1) 0

theorem onhFree_eq (n : ℕ) : onhFree n = GIdem.single 0 := rfl

/-- The graded projective `ONH_a e_a {k}`. -/
def projE (n : ℕ) (k : ℤ) : GIdem (onhGrading n) :=
  gelem (projector_mem n) projector_mul_projector k

/-- `E^{(a)} = ONH_a e_a {C(a,2)}`, `a = n+2`. -/
def divE (n : ℕ) : GIdem (onhGrading n) := projE n ((n+2).choose 2 : ℕ)

theorem deg61_eq {n : ℕ} (ℓ : Sq (n+2)) :
    Categorification.deg61 ℓ.1 = ((∑ ν, ℓ.1 ν : ℕ) : ℤ) - (((n+2).choose 2 : ℕ) : ℤ) := rfl

/-- (6.1) in `K₀`, before normalization: `[ONH_a] = ∑_{ℓ ∈ Sq(a)} q^{-2(|ℓ| - C(a,2))} [ONH_a e_a]`. -/
theorem of_onh_eq_sum (n : ℕ) :
    K0.of (GIdem.single 0 : GIdem (onhGrading n)) =
      ∑ ℓ : Sq (n+2), (T (0 - 2 * Categorification.deg61 ℓ.1) : LaurentPolynomial ℤ) •
        K0.of (projE n 0) :=
  of_elem_splitting (A := onhGrading n) unit_mem (one_mul 1) (projector_mem n)
    projector_mul_projector (Categorification.split61 n)
    (fun ℓ => 2 * Categorification.deg61 ℓ.1)
    (fun ℓ => sigma61_mem (Categorification.mem_Sq' ℓ))
    (fun ℓ => lam61_mem (Categorification.mem_Sq' ℓ)) 0

/-- **EKL (6.1)**, corrected, in `K₀(ONH_a)`: `[ONH_a] = ∑_{ℓ ∈ Sq(a)} q^{C(a,2) - 2|ℓ|} [E^{(a)}]`.
The summands are the classes of the decomposition `ONH_a ≅ ⊕_ℓ E^{(a)}{C(a,2) - 2|ℓ|}` given by
the row `(σ_ℓ)` and column `(λ_ℓ)` of `Categorification.split61`. -/
theorem eq_6_1_K0 (n : ℕ) :
    K0.of (GIdem.single 0 : GIdem (onhGrading n)) =
      ∑ ℓ : Sq (n+2), (T (((n+2).choose 2 : ℕ) - 2 * ((∑ ν, ℓ.1 ν : ℕ) : ℤ)) :
        LaurentPolynomial ℤ) • K0.of (divE n) := by
  rw [of_onh_eq_sum, show K0.of (divE n) = (T (((n+2).choose 2 : ℕ) : ℤ) :
    LaurentPolynomial ℤ) • K0.of (projE n 0) from of_elem _ _ _]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [smul_smul, ← T_add, deg61_eq]
  congr 2
  ring

/-- `[ONH_a e_a] ↦ q^{-2 C(a,2)}` under `K₀(ONH_a) ≃ ℤ[q,q⁻¹]`. -/
theorem onhK0Equiv_projE (n : ℕ) :
    onhK0Equiv n (K0.of (projE n 0)) = T (-(2 * (((n+2).choose 2 : ℕ) : ℤ))) := by
  have h := congrArg (onhK0Equiv n) (of_onh_eq_sum n)
  rw [onhK0Equiv_one, sum_T_length_eq, map_sum] at h
  simp only [map_smul, smul_eq_mul, ← Finset.sum_mul] at h
  refine mul_left_cancel₀ (sum_T_Sq_ne_zero n fun ℓ => 0 - 2 * Categorification.deg61 ℓ.1) ?_
  rw [← h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← T_add, deg61_eq]
  congr 1
  ring

/-- `[E^{(a)}] ↦ q^{-C(a,2)}`, a unit: `[E^{(a)}]` is a basis of `K₀(ONH_a)` over `ℤ[q,q⁻¹]`. -/
theorem onhK0Equiv_divE (n : ℕ) :
    onhK0Equiv n (K0.of (divE n)) = T (-(((n+2).choose 2 : ℕ) : ℤ)) := by
  rw [divE, projE, of_elem, map_smul, ← projE, onhK0Equiv_projE, smul_eq_mul, ← T_add]
  congr 1
  ring

/-! #### The printed exponents of (6.1) -/

/-- Evaluation at `q = -1`. -/
def negAug : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) (-1)

theorem negOne_zpow_two : ((-1 : ℤˣ) ^ (2 : ℤ)) = 1 := by
  rw [zpow_two, neg_one_mul, neg_neg]

theorem negAug_T_even (m : ℤ) : negAug (T (2 * m)) = 1 := by
  simp [negAug, _root_.zpow_mul, negOne_zpow_two]

theorem negAug_T_odd (m : ℤ) : negAug (T (2 * m + 1)) = -1 := by
  simp [negAug, _root_.zpow_add, _root_.zpow_mul, negOne_zpow_two]

/-- **Erratum to (6.1).** The printed decomposition `ONH_a ≅ ⊕_{ℓ ∈ Sq(a)} E^{(a)}{a-1-2|ℓ|}`
fails in `K₀` for `a = 3` (`n = 1`), for either sign convention of the shift (`ε = ±1`; the
statement holds for every `ε ∈ ℤ`): the correct exponents `C(3,2) - 2|ℓ|` (`eq_6_1_K0`) are
odd, the printed ones even (compare at `q = -1`). -/
theorem eq_6_1_printed_false (ε : ℤ) :
    K0.of (GIdem.single 0 : GIdem (onhGrading 1)) ≠
      ∑ ℓ : Sq 3, (T (ε * (3 - 1 - 2 * ((∑ ν, ℓ.1 ν : ℕ) : ℤ))) : LaurentPolynomial ℤ) •
        K0.of (divE 1) := by
  intro h
  rw [eq_6_1_K0] at h
  have h' := congrArg (onhK0Equiv 1) h
  simp only [map_sum, map_smul, smul_eq_mul, ← Finset.sum_mul, onhK0Equiv_divE] at h'
  have h'' := congrArg negAug (mul_right_cancel₀ (isUnit_T _).ne_zero h')
  simp only [map_sum] at h''
  have e1 : ∀ x : ℤ, negAug (T ((((1+2).choose 2 : ℕ) : ℤ) - 2 * x)) = -1 := fun x => by
    norm_num [Nat.choose]
    rw [show (3 : ℤ) - 2 * x = 2 * (1 - x) + 1 by ring, negAug_T_odd]
  have e2 : ∀ x : ℤ, negAug (T (ε * (3 - 1 - 2 * x))) = 1 := fun x => by
    rw [show ε * (3 - 1 - 2 * x) = 2 * (ε * (1 - x)) by ring, negAug_T_even]
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_coe, card_Sq] at h''
  norm_num [Nat.factorial] at h''

end Eq61

end OddMath.Frontier.OddCategorification
