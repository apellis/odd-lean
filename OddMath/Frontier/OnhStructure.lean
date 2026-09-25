import OddMath.Frontier.Categorification

/-! # The structure of `ONH_a`: corner ring, matrix form, primitivity of `e_a`

EKL arXiv:1111.1320v1.  `ONH_a = NilHeckeAction.Presented n`, `a = n+2`; `OΛ_a` is
`OddSymmetricKernel.kernelSubring n`; a written product `x * y` is `x` drawn on top of `y`.

* Corner ring (§4.1.2, (4.8)–(4.11)): `f ↦ e_a f e_a` is a ring isomorphism
  `OΛ_a ≃+* e_a ONH_a e_a` (`cornerEquiv`).  No anti-isomorphism and no `w_0`-twist occur:
  (4.10)–(4.11) give `(e_a g e_a)(e_a f e_a) = e_a g f e_a` for `g ∈ OΛ_a`.  Surjectivity and
  injectivity are read off in the faithful polynomial representation, where
  `e_a y e_a` acts by `p ↦ x^δ D_a(y(x^δ)) D_a(p)`.
* Matrix form (p. 42, paragraph after Theorem 4.15): the ring isomorphism
  `Mat_{Sq(a)}(OΛ_a) ≃+* ONH_a` sending the matrix with `f` in entry `(ℓ, ℓ')` to
  `σ_ℓ (e_a f e_a) λ_ℓ'` (`matrixEquiv`), from Lemma 4.13 and Theorem 4.15.  Together with
  (6.1) (`Categorification.eq_6_1`) this is the Morita equivalence `ONH_a ~ OΛ_a` of the abstract
  and §1.2.  The endomorphism ring of the progenerator `ONH_a e_a` is
  `End(ONH_a e_a) ≃+* (e_a ONH_a e_a)ᵐᵒᵖ ≃+* OΛ_aᵐᵒᵖ` (`endEquiv`, `endProjectorEquiv`).
* Primitivity (§6, p. 46: `E^{(a)}` is indecomposable): the only idempotents of the skew
  polynomial ring, hence of `OΛ_a` and of `e_a ONH_a e_a`, are `0` and `1`, by a lowest-degree
  argument; so `ONH_a e_a` admits no nontrivial direct sum decomposition
  (`leftIdeal_projector_indecomposable`). -/

namespace OddMath.Frontier.OnhStructure
open OddMath.SkewPolynomial (SkewPolynomial)
open NilHeckeAction ZeroHecke OnhPolynomial ThickDots Categorification

noncomputable section

/-! ## Idempotents of the skew polynomial ring -/

section Idempotent
variable {N : ℕ}

/-- Every monomial of `f * g` has degree at least `d + e` when those of `f`, `g` have degree
at least `d`, `e`. -/
theorem mul_lowDeg {f g : SkewPolynomial N} {d e : ℕ}
    (hf : ∀ a, f a ≠ 0 → d ≤ ∑ i, a i) (hg : ∀ b, g b ≠ 0 → e ≤ ∑ i, b i) (c : Fin N → ℕ)
    (hc : (f * g) c ≠ 0) : d + e ≤ ∑ i, c i := by
  change (OddMath.SkewPolynomial.mul f g) c ≠ 0 at hc
  rw [OddMath.SkewPolynomial.mul, Finsupp.sum_apply] at hc
  obtain ⟨a, ha, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  dsimp only at hc
  rw [Finsupp.sum_apply] at hc
  obtain ⟨b, hb, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.mp hc
  have h1 := hf a (Finsupp.mem_support_iff.mp ha)
  have h2 := hg b (Finsupp.mem_support_iff.mp hb)
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  omega

/-- The constant term is multiplicative. -/
theorem mul_apply_zero (f g : SkewPolynomial N) : (f * g) 0 = f 0 * g 0 := by
  change (OddMath.SkewPolynomial.mul f g) 0 = _
  rw [OddMath.SkewPolynomial.mul, Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single 0]
  · rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single 0]
    · rw [OddMath.SkewPolynomial.skewSign_zero_left, add_zero, mul_one]
      exact Finsupp.single_eq_same
    · intro b _ hb
      exact Finsupp.single_eq_of_ne (by simpa using hb)
    · intro hb
      rw [Finsupp.not_mem_support_iff.mp hb]
      simp
  · intro a _ ha
    rw [Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun b _ => Finsupp.single_eq_of_ne ?_
    intro h
    exact ha (funext fun i => by
      have := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; omega)
  · intro ha
    rw [Finsupp.not_mem_support_iff.mp ha, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp

/-- An idempotent without constant term vanishes: its lowest degree would double. -/
theorem eq_zero_of_idem {f : SkewPolynomial N} (h : f * f = f) (h0 : f 0 = 0) : f = 0 := by
  have base : ∀ c, f c ≠ 0 → 1 ≤ ∑ i, c i := by
    intro c hc
    have hc0 : c ≠ 0 := fun e => hc (e ▸ h0)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc0
    exact le_trans (Nat.one_le_iff_ne_zero.mpr hi)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i))
  have step : ∀ k, ∀ c, f c ≠ 0 → k + 1 ≤ ∑ i, c i := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      intro c hc
      have := mul_lowDeg ih ih c (by rwa [h])
      omega
  ext c
  by_contra hc
  have := step (∑ i, c i) c hc
  omega

/-- A subring of the skew polynomial ring (e.g. `OΛ_a`, or the whole ring) has no idempotents
other than `0` and `1`. -/
theorem idem_eq_zero_or_one (S : Subring (SkewPolynomial N)) {f : S} (h : f * f = f) :
    f = 0 ∨ f = 1 := by
  have hone : (1 : SkewPolynomial N) 0 = 1 := Finsupp.single_eq_same
  have hmul : ∀ g : S, g * g = g → (g : SkewPolynomial N) * g = g := fun g hg =>
    (congrArg Subtype.val hg : _)
  have h0 : (f : SkewPolynomial N) 0 * (f : SkewPolynomial N) 0 = (f : SkewPolynomial N) 0 := by
    rw [← mul_apply_zero, hmul f h]
  have hc : (f : SkewPolynomial N) 0 = 0 ∨ (f : SkewPolynomial N) 0 = 1 := by
    rcases mul_eq_zero.mp (show (f : SkewPolynomial N) 0 * ((f : SkewPolynomial N) 0 - 1) = 0 by
      rw [mul_sub, h0, mul_one, sub_self]) with e | e
    · exact Or.inl e
    · exact Or.inr (sub_eq_zero.mp e)
  rcases hc with hc | hc
  · exact Or.inl (Subtype.ext (eq_zero_of_idem (hmul f h) hc))
  · right
    have hg : (1 - f) * (1 - f) = 1 - f := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, h, sub_self, sub_zero]
    have hg0 : ((1 - f : S) : SkewPolynomial N) 0 = 0 := by
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, Finsupp.sub_apply, hone, hc, sub_self]
    have := eq_zero_of_idem (hmul _ hg) hg0
    exact (sub_eq_zero.mp (Subtype.ext this)).symm

end Idempotent

/-! ## The corner ring `e_a ONH_a e_a ≅ OΛ_a` -/

section Corner
variable {n : ℕ}
open LongestDivided SignedPermutation

/-- `OΛ_a`, the odd symmetric polynomials (joint kernel of the `∂_i`). -/
abbrev K (n : ℕ) := OddSymmetricKernel.kernelSubring n

theorem isIdempotentElem_projector (n : ℕ) : IsIdempotentElem (projector n) :=
  projector_mul_projector

/-- The corner ring `e_a ONH_a e_a`, with unit `e_a`. -/
abbrev Corner (n : ℕ) := (isIdempotentElem_projector n).Corner

/-- The dotted thick strand `e_a f e_a` (Definition 4.3). -/
def thick (n : ℕ) (f : SkewPolynomial (n+2)) : Presented n :=
  projector n * polyElem n f * projector n

/-- The sign `(-1)^{C(a,3)}` of Prop 3.5. -/
abbrev sign3 (n : ℕ) : ℤ := (-1 : ℤ)^((n+2).choose 3)

theorem sign3_mul_self : sign3 n * sign3 n = 1 := by rw [← mul_pow]; norm_num

theorem sign3_smul_smul {M : Type*} [AddCommGroup M] (x : M) : sign3 n • sign3 n • x = x := by
  rw [smul_smul, sign3_mul_self, one_smul]

/-- `e_a y e_a` acts by `p ↦ x^δ D_a(y(x^δ)) D_a(p)`. -/
theorem action_corner (y : Presented n) (p : SkewPolynomial (n+2)) :
    action n (projector n * y * projector n) p =
      staircase (n+2) * (D (n+2) (action n y (staircase (n+2))) * D (n+2) p) := by
  rw [action_mul_apply, action_mul_apply, action_projector p, map_zsmul,
    show action n y (staircase (n+2) * D (n+2) p) = action n y (staircase (n+2)) * D (n+2) p from
      NilHeckeRightKernel.action_right_mul_kernel n y ⟨_, LongestKernel.D_mem_kernel n p⟩ _,
    action_projector, map_zsmul, D_right_kernel n _ _ (LongestKernel.D_mem_kernel n p),
    mul_smul_comm, sign3_smul_smul]

/-- EKL (4.8) in the polynomial representation: `e_a f e_a` acts by
`p ↦ (-1)^{C(a,3)} x^δ f^{w_0} D_a(p)` for `f ∈ OΛ_a`. -/
theorem action_thick {f : SkewPolynomial (n+2)} (hf : f ∈ K n) (p : SkewPolynomial (n+2)) :
    action n (thick n f) p = sign3 n •
      (staircase (n+2) * (skewAction (LongestElementary.longest (n+2)) f * D (n+2) p)) := by
  rw [thick, projector_poly_projector f hf, map_zsmul, LinearMap.smul_apply, action_mul_apply,
    action_mul_apply, action_staircaseElem_apply, action_polyElem, action_DElem]

/-- The explicit preimage of `e_a y e_a`: `(-1)^{C(a,3)} (D_a(y(x^δ)))^{w_0}`. -/
def cornerPre (y : Presented n) : SkewPolynomial (n+2) :=
  sign3 n • skewAction (LongestElementary.longest (n+2)) (D (n+2) (action n y (staircase (n+2))))

theorem cornerPre_mem (y : Presented n) : cornerPre y ∈ K n :=
  Subring.zsmul_mem _ (LongestElementary.action_mem_kernel n _ (LongestKernel.D_mem_kernel n _)) _

/-- Every element of the corner ring is a dotted thick strand. -/
theorem thick_cornerPre (y : Presented n) :
    thick n (cornerPre y) = projector n * y * projector n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro p
  rw [action_thick (cornerPre_mem y), action_corner, cornerPre, map_zsmul,
    LongestElementary.action_involutive, smul_mul_assoc, mul_smul_comm, sign3_smul_smul]

theorem thick_eq_zero {f : SkewPolynomial (n+2)} (hf : f ∈ K n) (h : thick n f = 0) : f = 0 := by
  have hD := congrArg (fun z => D (n+2) (action n z (staircase (n+2)))) h
  simp only [action_thick hf, map_zero, LinearMap.zero_apply, D_staircase] at hD
  rw [mul_smul_comm, mul_one, mul_smul_comm, sign3_smul_smul,
    D_right_kernel n _ _ (LongestElementary.action_mem_kernel n f hf), D_staircase,
    smul_mul_assoc, one_mul] at hD
  have h0 := congrArg (fun x => sign3 n • x) hD
  simp only [sign3_smul_smul, smul_zero] at h0
  rw [← LongestElementary.action_involutive (n+2) f, h0, map_zero]

theorem thick_one : thick n 1 = projector n := by
  rw [thick, map_one, mul_one, projector_mul_projector]

theorem thick_add (f g : SkewPolynomial (n+2)) : thick n (f + g) = thick n f + thick n g := by
  rw [thick, map_add, mul_add, add_mul]; rfl

theorem projector_mul_thick (f : SkewPolynomial (n+2)) :
    projector n * thick n f = thick n f := by
  rw [thick, ← mul_assoc, ← mul_assoc, projector_mul_projector]

theorem thick_mul_projector (f : SkewPolynomial (n+2)) :
    thick n f * projector n = thick n f := by
  rw [thick, mul_assoc, projector_mul_projector]

/-- EKL (4.10)–(4.11) on `OΛ_a`. -/
theorem thick_mul_thick (f g : K n) :
    thick n f * thick n g = thick n (f * g : K n) :=
  thick_mul (f : SkewPolynomial (n+2)) g f.2

/-- `f ↦ e_a f e_a` as a ring homomorphism `OΛ_a →+* e_a ONH_a e_a`. -/
def thickHom (n : ℕ) : K n →+* Corner n where
  toFun f := ⟨thick n f, polyElem n f, rfl⟩
  map_one' := Subtype.ext thick_one
  map_mul' f g := Subtype.ext (thick_mul_thick f g).symm
  map_zero' := Subtype.ext (show thick n 0 = 0 by simp [thick])
  map_add' f g := Subtype.ext (thick_add (f : SkewPolynomial (n+2)) g)

theorem thickHom_bijective (n : ℕ) : Function.Bijective (thickHom n) := by
  refine ⟨fun f g hfg => ?_, ?_⟩
  · have h : thick n ((f - g : K n) : SkewPolynomial (n+2)) = 0 := by
      have e := congrArg Subtype.val hfg
      change thick n f = thick n g at e
      rw [AddSubgroupClass.coe_sub, thick, map_sub, mul_sub, sub_mul, ← thick, ← thick, e, sub_self]
    exact sub_eq_zero.mp (Subtype.ext (thick_eq_zero (f - g).2 h))
  rintro ⟨_, y, rfl⟩
  exact ⟨⟨cornerPre y, cornerPre_mem y⟩, Subtype.ext (thick_cornerPre y)⟩

/-- **Corner ring** (EKL §4.1.2, (4.8)–(4.11)): `OΛ_a ≃+* e_a ONH_a e_a`, `f ↦ e_a f e_a`.
It is a ring isomorphism, not an anti-isomorphism, and needs no `w_0`-twist. -/
def cornerEquiv (n : ℕ) : K n ≃+* Corner n :=
  RingEquiv.ofBijective (thickHom n) (thickHom_bijective n)

@[simp] theorem cornerEquiv_apply (f : K n) :
    (cornerEquiv n f).1 = projector n * polyElem n f * projector n := rfl

/-- By (4.9) the corner element is also `e_a f`. -/
theorem cornerEquiv_apply' (f : K n) :
    (cornerEquiv n f).1 = projector n * polyElem n f :=
  projector_poly_projector_eq _ f.2

theorem cornerEquiv_symm_apply (y : Presented n) :
    (((cornerEquiv n).symm ⟨_, y, rfl⟩ : K n) : SkewPolynomial (n+2)) = cornerPre y := by
  have h : cornerEquiv n ⟨cornerPre y, cornerPre_mem y⟩ = ⟨_, y, rfl⟩ :=
    Subtype.ext (thick_cornerPre y)
  rw [← h, RingEquiv.symm_apply_apply]

theorem projector_ne_zero (n : ℕ) : projector n ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val ((cornerEquiv n).map_one)
  have h0 := congrArg Subtype.val ((cornerEquiv n).map_zero)
  have : (1 : K n) = 0 := (cornerEquiv n).injective (Subtype.ext (h1.trans (h.trans h0.symm)))
  exact one_ne_zero (congrArg Subtype.val this)

end Corner

/-! ## `ONH_a` as a matrix ring over `OΛ_a` (p. 42) -/

section Matrix
variable {n : ℕ}
open ThickMatrixUnits

/-- The index set `Sq(a)` of (4.37); it has `a!` elements (`BoxPartitionCount.card_Sq`). -/
abbrev Idx (n : ℕ) := ↥(BoxPartitionCount.Sq (n+2))

theorem lam_mul_sigma (ℓ' ℓ : Idx n) :
    lam ℓ'.1 * sigma ℓ.1 = if ℓ' = ℓ then projector n else 0 := by
  rw [lemma_4_13 (mem_Sq' ℓ) (mem_Sq' ℓ')]
  by_cases h : ℓ' = ℓ
  · subst h; simp
  · rw [if_neg (fun e => h (Subtype.ext e)), if_neg h]

theorem sum_sigma_lam : ∑ ℓ : Idx n, sigma ℓ.1 * lam ℓ.1 = 1 := by
  rw [← thm_4_15_sum (n := n)]
  exact Finset.sum_coe_sort (BoxPartitionCount.Sq (n+2)) (fun ℓ => idem (n := n) ℓ)

/-- The matrix unit `σ_ℓ (e_a f e_a) λ_ℓ'`. -/
def matrixUnit (ℓ ℓ' : Idx n) (f : K n) : Presented n := sigma ℓ.1 * thick n f * lam ℓ'.1

theorem matrixUnit_zero (ℓ ℓ' : Idx n) : matrixUnit ℓ ℓ' 0 = 0 := by
  simp [matrixUnit, thick]

theorem matrixUnit_sum (ℓ ℓ' : Idx n) {ι : Type*} (s : Finset ι) (f : ι → K n) :
    matrixUnit ℓ ℓ' (∑ i ∈ s, f i) = ∑ i ∈ s, matrixUnit ℓ ℓ' (f i) := by
  simp only [matrixUnit, thick, AddSubmonoidClass.coe_finset_sum, map_sum, Finset.mul_sum,
    Finset.sum_mul]

theorem matrixUnit_mul (ℓ ℓ' m m' : Idx n) (f g : K n) :
    matrixUnit ℓ ℓ' f * matrixUnit m m' g = if ℓ' = m then matrixUnit ℓ m' (f * g) else 0 := by
  simp only [matrixUnit, mul_assoc]
  rw [← mul_assoc (lam ℓ'.1), lam_mul_sigma]
  split_ifs
  · rw [← mul_assoc (thick n f), thick_mul_projector, ← mul_assoc (thick n f),
      thick_mul_thick]
  · simp

theorem lam_matrixUnit_sigma (m ℓ ℓ' m' : Idx n) (f : K n) :
    lam m.1 * matrixUnit ℓ ℓ' f * sigma m'.1 = if m = ℓ ∧ ℓ' = m' then thick n f else 0 := by
  simp only [matrixUnit, mul_assoc]
  rw [← mul_assoc (lam m.1), lam_mul_sigma, lam_mul_sigma]
  by_cases h₁ : m = ℓ <;> by_cases h₂ : ℓ' = m' <;> simp [h₁, h₂, projector_mul_thick,
    thick_mul_projector, ← mul_assoc]

/-- `M ↦ ∑_{ℓ,ℓ'} σ_ℓ (e_a M_{ℓℓ'} e_a) λ_ℓ'`. -/
def toOnh (M : Matrix (Idx n) (Idx n) (K n)) : Presented n := ∑ ℓ, ∑ ℓ', matrixUnit ℓ ℓ' (M ℓ ℓ')

/-- The entries are recovered as `e_a M_{mm'} e_a = λ_m (toOnh M) σ_m'`. -/
theorem lam_toOnh_sigma (M : Matrix (Idx n) (Idx n) (K n)) (m m' : Idx n) :
    lam m.1 * toOnh M * sigma m'.1 = thick n (M m m') := by
  simp only [toOnh, Finset.mul_sum, Finset.sum_mul, lam_matrixUnit_sigma]
  rw [Finset.sum_eq_single m (fun ℓ _ h => by simp [Ne.symm h]) (by simp),
    Finset.sum_eq_single m' (fun ℓ' _ h => by simp [h]) (by simp), if_pos ⟨rfl, rfl⟩]

theorem matrixUnit_mul_toOnh (ℓ ℓ' : Idx n) (f : K n) (N : Matrix (Idx n) (Idx n) (K n)) :
    matrixUnit ℓ ℓ' f * toOnh N = ∑ m', matrixUnit ℓ m' (f * N ℓ' m') := by
  rw [toOnh, Finset.mul_sum, Finset.sum_eq_single ℓ']
  · rw [Finset.mul_sum]
    simp only [matrixUnit_mul, if_true]
  · intro m _ h
    rw [Finset.mul_sum]
    simp [matrixUnit_mul, Ne.symm h]
  · simp

theorem toOnh_mul (M N : Matrix (Idx n) (Idx n) (K n)) : toOnh (M * N) = toOnh M * toOnh N := by
  symm
  calc toOnh M * toOnh N = ∑ ℓ, ∑ ℓ', ∑ m', matrixUnit ℓ m' (M ℓ ℓ' * N ℓ' m') := by
        rw [toOnh, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ℓ' _ => matrixUnit_mul_toOnh ℓ ℓ' _ N
    _ = toOnh (M * N) := by
        simp only [toOnh, Matrix.mul_apply, matrixUnit_sum]
        exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_comm

theorem toOnh_one : toOnh (1 : Matrix (Idx n) (Idx n) (K n)) = 1 := by
  simp only [toOnh, Matrix.one_apply, apply_ite (matrixUnit _ _), matrixUnit_zero,
    Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← sum_sigma_lam]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [matrixUnit, OneMemClass.coe_one, thick_one, mul_assoc, ThickMatrixUnits.projector_mul_lam]

theorem toOnh_add (M N : Matrix (Idx n) (Idx n) (K n)) : toOnh (M + N) = toOnh M + toOnh N := by
  simp only [toOnh, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun ℓ' _ => ?_
  simp only [matrixUnit, AddMemClass.coe_add, thick_add, mul_add, add_mul]

theorem expand (z : Presented n) :
    z = ∑ ℓ : Idx n, ∑ ℓ' : Idx n, sigma ℓ.1 * lam ℓ.1 * z * (sigma ℓ'.1 * lam ℓ'.1) := by
  calc z = (∑ ℓ : Idx n, sigma ℓ.1 * lam ℓ.1) * z * (∑ ℓ' : Idx n, sigma ℓ'.1 * lam ℓ'.1) := by
        rw [sum_sigma_lam, one_mul, mul_one]
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ℓ _ => Finset.mul_sum _ _ _

/-- The ring homomorphism `Mat_{Sq(a)}(OΛ_a) → ONH_a`. -/
def toOnhHom (n : ℕ) : Matrix (Idx n) (Idx n) (K n) →+* Presented n where
  toFun := toOnh
  map_one' := toOnh_one
  map_mul' := toOnh_mul
  map_zero' := by simp [toOnh, matrixUnit_zero]
  map_add' := toOnh_add

theorem toOnhHom_bijective (n : ℕ) : Function.Bijective (toOnhHom n) := by
  refine ⟨fun M N h => ?_, fun z => ?_⟩
  · funext m m'
    have e := congrArg (fun z => lam m.1 * z * sigma m'.1) h
    simp only [toOnhHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      lam_toOnh_sigma] at e
    exact (cornerEquiv n).injective (Subtype.ext e)
  · refine ⟨fun ℓ ℓ' => ⟨cornerPre (lam ℓ.1 * z * sigma ℓ'.1), cornerPre_mem _⟩, ?_⟩
    change toOnh _ = z
    conv_rhs => rw [expand z]
    simp only [toOnh, matrixUnit, thick_cornerPre]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun ℓ' _ => ?_
    simp only [mul_assoc, ThickMatrixUnits.projector_mul_lam]
    rw [← mul_assoc (projector n), ThickMatrixUnits.projector_mul_lam]

/-- **EKL p. 42** (paragraph after Theorem 4.15): `ONH_a ≅ Mat_{a!}(OΛ_a)`.  The matrix with `f`
in entry `(ℓ, ℓ')` goes to `σ_ℓ (e_a f e_a) λ_ℓ'`; no twist of `f` is needed. -/
def matrixEquiv (n : ℕ) : Matrix (Idx n) (Idx n) (K n) ≃+* Presented n :=
  RingEquiv.ofBijective (toOnhHom n) (toOnhHom_bijective n)

theorem matrixEquiv_apply (M : Matrix (Idx n) (Idx n) (K n)) :
    matrixEquiv n M = ∑ ℓ, ∑ ℓ', sigma ℓ.1 * (projector n * polyElem n (M ℓ ℓ') * projector n) *
      lam ℓ'.1 := rfl

/-- The inverse reads off entries: `e_a (matrixEquiv⁻¹ z)_{ℓℓ'} e_a = λ_ℓ z σ_ℓ'`. -/
theorem thick_matrixEquiv_symm (z : Presented n) (ℓ ℓ' : Idx n) :
    thick n ((matrixEquiv n).symm z ℓ ℓ') = lam ℓ.1 * z * sigma ℓ'.1 := by
  conv_rhs => rw [← (matrixEquiv n).apply_symm_apply z]
  exact (lam_toOnh_sigma _ ℓ ℓ').symm

theorem card_Idx (n : ℕ) : Fintype.card (Idx n) = (n+2).factorial := by
  rw [Fintype.card_coe, BoxPartitionCount.card_Sq]

end Matrix

/-! ## Endomorphisms of `R e` -/

section EndCorner
variable {R : Type*} [Ring R] {e : R} (he : IsIdempotentElem e)

/-- The generator `e ∈ R e`. -/
def gen : leftIdeal e := ⟨e, he.eq⟩

theorem eq_smul_gen (x : leftIdeal e) : x = x.1 • gen he :=
  Subtype.ext (show x.1 = x.1 * e from x.2.symm)

variable {he} in
theorem mem_corner_of_end (φ : Module.End R (leftIdeal e)) :
    (φ (gen he)).1 ∈ Subsemigroup.corner e := by
  refine (Subsemigroup.mem_corner_iff he).mpr ⟨?_, (φ (gen he)).2⟩
  have h : φ (gen he) = e • φ (gen he) := by
    conv_lhs => rw [eq_smul_gen he (gen he), LinearMap.map_smul]
    rfl
  exact (congrArg Subtype.val h).symm

/-- Right multiplication by `c ∈ e R e`, an endomorphism of the left module `R e`. -/
def rmul (c : he.Corner) : Module.End R (leftIdeal e) where
  toFun x := ⟨x.1 * c.1, by
    change x.1 * c.1 * e = x.1 * c.1
    rw [mul_assoc, ((Subsemigroup.mem_corner_iff he).mp c.2).2]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 c.1)
  map_smul' r x := Subtype.ext (mul_assoc r x.1 c.1)

/-- `End_R(R e) ≃+* (e R e)ᵐᵒᵖ`, `φ ↦ φ(e)`, inverse: right multiplication. -/
def endEquiv : Module.End R (leftIdeal e) ≃+* he.Cornerᵐᵒᵖ where
  toFun φ := MulOpposite.op ⟨(φ (gen he)).1, mem_corner_of_end φ⟩
  invFun c := rmul he c.unop
  left_inv φ := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.1 * (φ (gen he)).1 = (φ x).1
    conv_rhs => rw [eq_smul_gen he x, LinearMap.map_smul]
    rfl
  right_inv c := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact ((Subsemigroup.mem_corner_iff he).mp c.unop.2).1
  map_mul' φ ψ := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (φ (ψ (gen he))).1 = (ψ (gen he)).1 * (φ (gen he)).1
    conv_lhs => rw [eq_smul_gen he (ψ (gen he)), LinearMap.map_smul]
    rfl
  map_add' φ ψ := rfl

theorem endEquiv_apply (φ : Module.End R (leftIdeal e)) :
    (endEquiv he φ).unop.1 = (φ (gen he)).1 := rfl

end EndCorner

section EndOnh
variable {n : ℕ}

/-- **Morita** (EKL abstract, §1.2): `End_{ONH_a}(ONH_a e_a) ≃+* (OΛ_a)ᵐᵒᵖ`, `φ ↦ φ(e_a)`. -/
def endProjectorEquiv (n : ℕ) : Module.End (Presented n) (leftIdeal (projector n)) ≃+* (K n)ᵐᵒᵖ :=
  (endEquiv (isIdempotentElem_projector n)).trans (RingEquiv.op (cornerEquiv n).symm)

theorem thick_endProjectorEquiv (φ : Module.End (Presented n) (leftIdeal (projector n))) :
    thick n (endProjectorEquiv n φ).unop = (φ (gen (isIdempotentElem_projector n))).1 := by
  change (cornerEquiv n ((cornerEquiv n).symm (endEquiv _ φ).unop)).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end EndOnh

/-! ## Primitivity of `e_a` (§6, p. 46) -/

section Primitive
variable {n : ℕ}

/-- `OΛ_a` has no idempotents other than `0` and `1`. -/
theorem kernel_idem {f : K n} (h : f * f = f) : f = 0 ∨ f = 1 :=
  idem_eq_zero_or_one (K n) h

/-- The corner ring `e_a ONH_a e_a` has no idempotents other than `0` and `e_a`. -/
theorem corner_idem {z : Corner n} (h : z * z = z) : z = 0 ∨ z = 1 := by
  have hf : (cornerEquiv n).symm z * (cornerEquiv n).symm z = (cornerEquiv n).symm z := by
    rw [← map_mul, h]
  rcases kernel_idem hf with hf | hf
  · left
    rw [← (cornerEquiv n).apply_symm_apply z, hf, map_zero]
  · right
    rw [← (cornerEquiv n).apply_symm_apply z, hf, map_one]

/-- `e_a` is primitive: an idempotent `e_a y e_a` is `0` or `e_a`. -/
theorem projector_primitive (y : Presented n)
    (h : projector n * y * projector n * (projector n * y * projector n) =
      projector n * y * projector n) :
    projector n * y * projector n = 0 ∨ projector n * y * projector n = projector n := by
  have hz := corner_idem (n := n) (z := ⟨_, y, rfl⟩) (Subtype.ext h)
  rcases hz with hz | hz
  · exact Or.inl (congrArg Subtype.val hz)
  · exact Or.inr (congrArg Subtype.val hz)

/-- The idempotent endomorphisms of `ONH_a e_a` are `0` and `1`. -/
theorem end_idem {φ : Module.End (Presented n) (leftIdeal (projector n))} (h : φ * φ = φ) :
    φ = 0 ∨ φ = 1 := by
  have hf : (endProjectorEquiv n φ).unop * (endProjectorEquiv n φ).unop =
      (endProjectorEquiv n φ).unop := by
    rw [← MulOpposite.unop_mul, ← map_mul, h]
  rcases kernel_idem hf with hf | hf
  · left
    apply (endProjectorEquiv n).injective
    rw [map_zero, ← MulOpposite.op_unop (endProjectorEquiv n φ), hf, MulOpposite.op_zero]
  · right
    apply (endProjectorEquiv n).injective
    rw [map_one, ← MulOpposite.op_unop (endProjectorEquiv n φ), hf, MulOpposite.op_one]

/-- **EKL §6, p. 46**: `E^{(a)} = ONH_a e_a` is indecomposable.  It is nonzero, and in any
decomposition `ONH_a e_a = N₁ ⊕ N₂` into left submodules one summand vanishes. -/
theorem leftIdeal_projector_indecomposable (N₁ N₂ : Submodule (Presented n) (Presented n))
    (hsup : N₁ ⊔ N₂ = leftIdeal (projector n)) (hinf : N₁ ⊓ N₂ = ⊥) : N₁ = ⊥ ∨ N₂ = ⊥ := by
  set P := projector n
  have hP : P ∈ N₁ ⊔ N₂ := by rw [hsup]; exact projector_mul_projector
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hP
  have hu' : u * P = u := (hsup ▸ Submodule.mem_sup_left hu : u ∈ leftIdeal P)
  have hv' : v * P = v := (hsup ▸ Submodule.mem_sup_right hv : v ∈ leftIdeal P)
  have zero_of (a b : Presented n) (ha : a ∈ N₁) (hb : b ∈ N₂) (hab : a * b ∈ N₁) :
      a * b = 0 := by
    have : a * b ∈ N₁ ⊓ N₂ := ⟨hab, N₂.smul_mem a hb⟩
    rwa [hinf, Submodule.mem_bot] at this
  have huv0 : u * v = 0 := by
    refine zero_of u v hu hv ?_
    have e : u * v = u - u * u := by
      rw [eq_sub_iff_add_eq, ← mul_add, add_comm, huv, hu']
    rw [e]
    exact N₁.sub_mem hu (N₁.smul_mem u hu)
  have hvu0 : v * u = 0 := by
    have : v * u ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.smul_mem v hu, ?_⟩
      have e : v * u = v - v * v := by
        rw [eq_sub_iff_add_eq, ← mul_add, huv, hv']
      rw [e]
      exact N₂.sub_mem hv (N₂.smul_mem v hv)
    rwa [hinf, Submodule.mem_bot] at this
  have huu : u * u = u := by
    have := congrArg (u * ·) huv
    simp only [mul_add, huv0, add_zero, hu'] at this
    exact this
  have hvv : v * v = v := by
    have := congrArg (v * ·) huv
    simp only [mul_add, hvu0, zero_add, hv'] at this
    exact this
  have htu : P * u * P = P * u := by rw [mul_assoc, hu']
  have hidem : P * u * P * (P * u * P) = P * u * P := by
    rw [htu, mul_assoc, ← mul_assoc u P u, hu', huu]
  have le_of (N : Submodule (Presented n) (Presented n)) (hN : P ∈ N) :
      leftIdeal P ≤ N := fun x hx => by
    rw [← (hx : x * P = x)]; exact N.smul_mem x hN
  rcases projector_primitive u hidem with h0 | h1
  · -- `e_a u = 0`, so `u = u u = u e_a u = 0` and `e_a = v ∈ N₂`.
    left
    rw [htu] at h0
    have hu0 : u = 0 :=
      calc u = u * u := huu.symm
        _ = u * P * u := by rw [hu']
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
    have hPv : P ∈ N₂ := by rw [← huv, hu0, zero_add]; exact hv
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl ((hsup ▸ le_sup_left : N₁ ≤ leftIdeal P).trans (le_of N₂ hPv))
  · -- `e_a u = e_a`, so `e_a v = 0`, `v = 0` and `e_a = u ∈ N₁`.
    right
    rw [htu] at h1
    have hPv : P * v = 0 := by
      have := congrArg (P * ·) huv
      simp only [mul_add, h1, projector_mul_projector, P] at this
      exact left_eq_add.mp this.symm
    have hv0 : v = 0 :=
      calc v = v * v := hvv.symm
        _ = v * P * v := by rw [hv']
        _ = 0 := by rw [mul_assoc, hPv, mul_zero]
    have hPu : P ∈ N₁ := by rw [← huv, hv0, add_zero]; exact hu
    rw [eq_bot_iff, ← hinf]
    exact le_inf ((hsup ▸ le_sup_right : N₂ ≤ leftIdeal P).trans (le_of N₁ hPu)) le_rfl

theorem leftIdeal_projector_ne_bot (n : ℕ) : leftIdeal (projector n) ≠ ⊥ := by
  intro h
  have hP : projector n ∈ leftIdeal (projector n) := projector_mul_projector
  rw [h, Submodule.mem_bot] at hP
  exact projector_ne_zero n hP

end Primitive

end

end OddMath.Frontier.OnhStructure
