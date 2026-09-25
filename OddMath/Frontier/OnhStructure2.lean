import OddMath.Frontier.OnhWindow

/-! # The inclusion `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`

EKL arXiv:1111.1320v1, §6, p. 46 (and §3.2.4): placing diagrams side by side gives an inclusion
`ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`.  Here `a = m+2`, `b = m'+2`, `ONH_{a+b} = Presented (m+2+m')`,
`ι_L = windowHom` at offset `0` and `ι_R = windowHom` at offset `a`.

* `tensorMap : ONH_a ⊗_ℤ ONH_b →ₗ[ℤ] ONH_{a+b}`, `x ⊗ y ↦ ι_L(x) ι_R(y)`, is injective
  (`tensorMap_injective`): the PBW basis tensor `x^A ∂_w ⊗ x^B ∂_v`
  (`NilHeckeBasis.basis`, Prop 2.11) goes to `± x^{A ⊔ B} ∂_{w × v}`, and
  `(A, w, B, v) ↦ (A ⊔ B, w × v)` is injective; `ℓ(w × v) = ℓ(w) + ℓ(v)`
  (`length_blockPerm`).
* The image `tensorImage` is a subring of `ONH_{a+b}` containing `ι_L(ONH_a)` and `ι_R(ONH_b)`,
  and `tensorEquiv : ONH_a ⊗_ℤ ONH_b ≃ₗ[ℤ] range tensorMap`.
* The multiplication is the super tensor product one (`tensorMap_mul`):
  `(x ⊗ y)(x' ⊗ y') = (-1)^{|y||x'|} x x' ⊗ y y'` for `y`, `x'` products of `k`, `k'` generators
  (`OnhWindow.Homog`).  Dots have degree `2` and crossings degree `-2`, so the parity of the
  number of generators is the super-degree `deg/2 mod 2`. -/

namespace OddMath.Frontier.OnhStructure
open NilHeckeAction NilCoxeterWords NilHeckeBasis OnhWindow
open scoped TensorProduct

noncomputable section

variable {m m' : ℕ}

/-! ## The two windows -/

theorem window_left_le (m m' : ℕ) : 0 + (m+2) ≤ m+2+m'+2 := by omega
theorem window_right_le (m m' : ℕ) : (m+2) + (m'+2) ≤ m+2+m'+2 := by omega

/-- `ι_L : ONH_a → ONH_{a+b}`, strands `[0, a)`. -/
def incL (m m' : ℕ) : Presented m →+* Presented (m+2+m') :=
  windowHom m (m+2+m') 0 (window_left_le m m')

/-- `ι_R : ONH_b → ONH_{a+b}`, strands `[a, a+b)`. -/
def incR (m m' : ℕ) : Presented m' →+* Presented (m+2+m') :=
  windowHom m' (m+2+m') (m+2) (window_right_le m m')

/-! ## Dots -/

theorem dotMonomial_eq_prod_ofFn {n : ℕ} (A : Fin (n+2) → ℕ) :
    dotMonomial A = (List.ofFn fun i => dot n i ^ A i).prod := by
  rw [dotMonomial, List.ofFn_eq_map]

/-- The concatenated exponent `A ⊔ B` on the strands `[0, a+b)`. -/
def appendExp (A : Fin (m+2) → ℕ) (B : Fin (m'+2) → ℕ) : Fin (m+2+m'+2) → ℕ :=
  Fin.append (m := m+2) (n := m'+2) A B

/-- `ι_L(x^A) ι_R(x^B) = x^{A ⊔ B}`, exactly. -/
theorem incL_dotMonomial_mul_incR (A : Fin (m+2) → ℕ) (B : Fin (m'+2) → ℕ) :
    incL m m' (dotMonomial A) * incR m m' (dotMonomial B) =
      dotMonomial (appendExp A B) := by
  rw [dotMonomial_eq_prod_ofFn, dotMonomial_eq_prod_ofFn, dotMonomial_eq_prod_ofFn,
    List.ofFn_add (m := m+2) (n := m'+2), List.prod_append, map_list_prod, map_list_prod,
    List.map_ofFn, List.map_ofFn]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply, map_pow, incL, windowHom_dot, appendExp, Fin.append_left]
    congr 2
  · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    simp only [Function.comp_apply, map_pow, incR, windowHom_dot, appendExp, Fin.append_right]
    congr 2
    exact Fin.ext (by simp [add_comm])

/-! ## Block permutations -/

/-- `w × v`: `w` on the strands `[0, a)`, `v` on `[a, a+b)`. -/
def blockPerm (w : Perm m) (v : Perm m') : Perm (m+2+m') :=
  (finSumFinEquiv (m := m+2) (n := m'+2)).permCongr (Equiv.Perm.sumCongr w v)

@[simp] theorem blockPerm_castAdd (w : Perm m) (v : Perm m') (i : Fin (m+2)) :
    blockPerm w v (Fin.castAdd (m'+2) i) = Fin.castAdd (m'+2) (w i) := by
  show (finSumFinEquiv (m := m+2) (n := m'+2)) (Equiv.Perm.sumCongr w v
    ((finSumFinEquiv (m := m+2) (n := m'+2)).symm (Fin.castAdd (m'+2) i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

@[simp] theorem blockPerm_natAdd (w : Perm m) (v : Perm m') (j : Fin (m'+2)) :
    blockPerm w v (Fin.natAdd (m+2) j) = Fin.natAdd (m+2) (v j) := by
  show (finSumFinEquiv (m := m+2) (n := m'+2)) (Equiv.Perm.sumCongr w v
    ((finSumFinEquiv (m := m+2) (n := m'+2)).symm (Fin.natAdd (m+2) j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem blockPerm_mul (w w' : Perm m) (v v' : Perm m') :
    blockPerm (w * w') (v * v') = blockPerm w v * blockPerm w' v' := by
  simp only [blockPerm, ← Equiv.Perm.sumCongr_mul]
  exact Equiv.ext fun x => by simp [Equiv.Perm.mul_apply]

theorem blockPerm_one : blockPerm (1 : Perm m) (1 : Perm m') = 1 := by
  simp only [blockPerm, Equiv.Perm.sumCongr_one]
  exact Equiv.ext fun x => by simp

theorem simple_shiftL (i : Fin (m+1)) :
    simple (shiftIndex (window_left_le m m') i) = blockPerm (simple i) (1 : Perm m') := by
  rw [blockPerm, simple, simple, Equiv.Perm.sumCongr_swap_one, Equiv.permCongr_def,
    Equiv.symm_trans_swap_trans, finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
  congr 1

theorem simple_shiftR (i : Fin (m'+1)) :
    simple (shiftIndex (window_right_le m m') i) = blockPerm (1 : Perm m) (simple i) := by
  rw [blockPerm, simple, simple, Equiv.Perm.sumCongr_one_swap, Equiv.permCongr_def,
    Equiv.symm_trans_swap_trans, finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
  congr 1 <;> exact Fin.ext (by
    simp only [Fin.coe_castSucc, Fin.val_succ, Fin.coe_natAdd, shiftIndex_val]; omega)

theorem permutation_mapL (u : Word m) :
    permutation (u.map (shiftIndex (window_left_le m m'))) =
      blockPerm (permutation u) (1 : Perm m') := by
  induction u with
  | nil => exact blockPerm_one.symm
  | cons i u ih =>
    rw [List.map_cons, permutation, permutation, ih, simple_shiftL, ← blockPerm_mul, one_mul]

theorem permutation_mapR (u : Word m') :
    permutation (u.map (shiftIndex (window_right_le m m'))) =
      blockPerm (1 : Perm m) (permutation u) := by
  induction u with
  | nil => exact blockPerm_one.symm
  | cons i u ih =>
    rw [List.map_cons, permutation, permutation, ih, simple_shiftR, ← blockPerm_mul, one_mul]

/-- `ℓ(w × v) = ℓ(w) + ℓ(v)`: the two blocks contribute no mixed inversions. -/
theorem length_blockPerm (w : Perm m) (v : Perm m') :
    length (blockPerm w v) = length w + length v := by
  change (∑ a : Fin ((m+2)+(m'+2)), ∑ b : Fin ((m+2)+(m'+2)),
    if a < b ∧ blockPerm w v b < blockPerm w v a then 1 else 0) = _
  simp only [Fin.sum_univ_add (a := m+2) (b := m'+2), blockPerm_castAdd, blockPerm_natAdd,
    Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  have h₁ : ∀ (i : Fin (m+2)) (j : Fin (m'+2)),
      (if (i : ℕ) < m+2+j ∧ m+2+(v j : ℕ) < w i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := (w i).isLt; omega
  have h₂ : ∀ (i : Fin (m'+2)) (j : Fin (m+2)),
      (if m+2+(i : ℕ) < j ∧ (w j : ℕ) < m+2+v i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := j.isLt; omega
  simp only [h₁, h₂, Finset.sum_const_zero, add_zero, zero_add, length, Fin.lt_iff_val_lt_val]

/-- `ι_L(∂_w) ι_R(∂_v) = ± ∂_{w × v}`. -/
theorem incL_mul_incR_divided (w : Perm m) (v : Perm m') :
    Signed (incL m m' (dividedElement w) * incR m m' (dividedElement v))
      (dividedElement (blockPerm w v)) := by
  rw [dividedElement, dividedElement, incL, incR, windowHom_product, windowHom_product,
    ← product_append]
  have hp : permutation ((chosenWord w).map (shiftIndex (window_left_le m m')) ++
      (chosenWord v).map (shiftIndex (window_right_le m m'))) = blockPerm w v := by
    rw [permutation_append, permutation_mapL, permutation_mapR, chosenWord_permutation,
      chosenWord_permutation, ← blockPerm_mul, mul_one, one_mul]
  have hr : Reduced ((chosenWord w).map (shiftIndex (window_left_le m m')) ++
      (chosenWord v).map (shiftIndex (window_right_le m m'))) := by
    unfold Reduced
    rw [hp, length_blockPerm, List.length_append, List.length_map, List.length_map,
      chosenWord_length, chosenWord_length]
  have := reduced_dividedElement _ hr
  rwa [hp] at this

/-! ## The PBW basis tensors -/

theorem homog_product (u : Word m) : Homog 0 (m+2) u.length (product u) := by
  induction u with
  | nil => exact Homog.one
  | cons i u ih =>
    have := (Homog.gen (isGen_full_crossing i)).mul ih
    rw [List.length_cons, Nat.add_comm u.length 1]
    exact this

theorem homog_dotMonomial (A : Fin (m+2) → ℕ) : ∃ k, Homog 0 (m+2) k (dotMonomial A) := by
  have hpow : ∀ (j : Fin (m+2)) (e : ℕ), Homog 0 (m+2) e (dot m j ^ e) := by
    intro j e
    induction e with
    | zero => exact Homog.one
    | succ e ih => rw [pow_succ]; exact ih.mul (Homog.gen (isGen_full_dot j))
  rw [dotMonomial]
  induction List.finRange (m+2) with
  | nil => exact ⟨0, Homog.one⟩
  | cons j l ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨_, (hpow j (A j)).mul hk⟩

theorem signed_neg_one_pow_mul {R : Type*} [Ring R] (k : ℕ) (x : R) : Signed ((-1)^k * x) x := by
  rcases neg_one_pow_eq_or R k with h | h
  · exact Or.inl (by rw [h, one_mul])
  · exact Or.inr (by rw [h, neg_one_mul])

/-- `ι_L(x^A ∂_w) ι_R(x^B ∂_v) = ± x^{A ⊔ B} ∂_{w × v}`. -/
theorem incL_mul_incR_basis (A : Fin (m+2) → ℕ) (w : Perm m) (B : Fin (m'+2) → ℕ)
    (v : Perm m') :
    Signed (incL m m' (basisElement (A, w)) * incR m m' (basisElement (B, v)))
      (basisElement (appendExp A B, blockPerm w v)) := by
  obtain ⟨k, hk⟩ := homog_dotMonomial B
  have hsc := windowHom_supercomm (h := window_left_le m m') (h' := window_right_le m m')
    (homog_product (chosenWord w)) hk (by omega)
  have hX : Signed (incL m m' (dividedElement w) * incR m m' (dotMonomial B))
      (incR m m' (dotMonomial B) * incL m m' (dividedElement w)) := by
    rw [incL, incR, dividedElement, hsc]
    exact signed_neg_one_pow_mul _ _
  have h1 := ((Signed.refl (incL m m' (dotMonomial A))).mul hX).mul
    (Signed.refl (incR m m' (dividedElement v)))
  have h2 := (Signed.refl (incL m m' (dotMonomial A) * incR m m' (dotMonomial B))).mul
    (incL_mul_incR_divided w v)
  simp only [basisElement, map_mul]
  rw [← incL_dotMonomial_mul_incR]
  have e1 : incL m m' (dotMonomial A) * incL m m' (dividedElement w) *
      (incR m m' (dotMonomial B) * incR m m' (dividedElement v)) =
      incL m m' (dotMonomial A) * (incL m m' (dividedElement w) * incR m m' (dotMonomial B)) *
        incR m m' (dividedElement v) := by simp only [mul_assoc]
  have e2 : incL m m' (dotMonomial A) * (incR m m' (dotMonomial B) * incL m m' (dividedElement w)) *
        incR m m' (dividedElement v) =
      incL m m' (dotMonomial A) * incR m m' (dotMonomial B) *
        (incL m m' (dividedElement w) * incR m m' (dividedElement v)) := by simp only [mul_assoc]
  rw [e1]
  refine h1.trans ?_
  rw [e2]
  exact h2

/-! ## Injectivity -/

/-- A linear map sending a basis to `±` an injectively indexed part of a basis is injective. -/
theorem injective_of_signed_basis {ι ι' M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (b : Basis ι ℤ M) (b' : Basis ι' ℤ M') (T : M →ₗ[ℤ] M') (φ : ι → ι')
    (hφ : Function.Injective φ) (hT : ∀ i, Signed (T (b i)) (b' (φ i))) :
    Function.Injective T := by
  have hu : ∀ i, ∃ u : ℤˣ, T (b i) = u • b' (φ i) := by
    intro i
    rcases hT i with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h, Units.neg_smul]⟩
  choose u hu using hu
  have hli : LinearIndependent ℤ (T ∘ b) := by
    have : T ∘ b = u • (b' ∘ φ) := funext fun i => hu i
    rw [this]
    exact (b'.linearIndependent.comp φ hφ).units_smul u
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h0 : Finsupp.linearCombination ℤ (T ∘ b) (b.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, b.linearCombination_repr]
    exact hx
  have := linearIndependent_iff.mp hli _ h0
  rw [← b.linearCombination_repr x, this, map_zero]

/-- `x ⊗ y ↦ ι_L(x) ι_R(y)`. -/
def tensorMap (m m' : ℕ) : Presented m ⊗[ℤ] Presented m' →ₗ[ℤ] Presented (m+2+m') :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun x y => incL m m' x * incR m m' y)
    (fun x₁ x₂ y => by simp only [map_add, add_mul])
    (fun c x y => by simp only [map_zsmul, smul_mul_assoc])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun c x y => by simp only [map_zsmul, mul_smul_comm]))

@[simp] theorem tensorMap_tmul (x : Presented m) (y : Presented m') :
    tensorMap m m' (x ⊗ₜ y) = incL m m' x * incR m m' y := rfl

theorem blockIndex_injective :
    Function.Injective (fun i : ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m') =>
      (appendExp i.1.1 i.2.1, blockPerm i.1.2 i.2.2)) := by
  rintro ⟨⟨A, w⟩, ⟨B, v⟩⟩ ⟨⟨A', w'⟩, ⟨B', v'⟩⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hA, hw⟩ := h
  have eA : A = A' := funext fun i => by
    simpa [appendExp] using congrFun hA (Fin.castAdd (m'+2) i)
  have eB : B = B' := funext fun j => by
    simpa [appendExp] using congrFun hA (Fin.natAdd (m+2) j)
  have ew : w = w' := Equiv.ext fun i => by
    have := congrArg (fun p : Perm (m+2+m') => p (Fin.castAdd (m'+2) i)) hw
    simpa using this
  have ev : v = v' := Equiv.ext fun j => by
    have := congrArg (fun p : Perm (m+2+m') => p (Fin.natAdd (m+2) j)) hw
    simpa using this
  rw [eA, eB, ew, ev]

/-- **EKL §6, p. 46**: `ONH_a ⊗_ℤ ONH_b → ONH_{a+b}`, `x ⊗ y ↦ ι_L(x) ι_R(y)`, is injective. -/
theorem tensorMap_injective (m m' : ℕ) : Function.Injective (tensorMap m m') := by
  refine injective_of_signed_basis ((basis m).tensorProduct (basis m')) (basis (m+2+m'))
    (tensorMap m m') _ blockIndex_injective ?_
  rintro ⟨⟨A, w⟩, ⟨B, v⟩⟩
  rw [Basis.tensorProduct_apply, tensorMap_tmul, basis_apply, basis_apply, basis_apply]
  exact incL_mul_incR_basis A w B v

/-! ## The super tensor product rule -/

theorem tensorMap_one : tensorMap m m' (1 ⊗ₜ 1) = 1 := by
  rw [tensorMap_tmul, map_one, map_one, one_mul]

/-- The multiplication of `ONH_{a+b}` restricted to `ONH_a ⊗ ONH_b` is the super tensor product:
`(x ⊗ y)(x' ⊗ y') = (-1)^{|y||x'|} x x' ⊗ y y'`, for `y` a product of `k` generators and `x'` of
`k'`. -/
theorem tensorMap_mul {x x' : Presented m} {y y' : Presented m'} {k k' : ℕ}
    (hy : Homog 0 (m'+2) k y) (hx' : Homog 0 (m+2) k' x') :
    tensorMap m m' (x ⊗ₜ y) * tensorMap m m' (x' ⊗ₜ y') =
      (-1) ^ (k * k') * tensorMap m m' ((x * x') ⊗ₜ (y * y')) := by
  have hsc := windowHom_supercomm (h := window_left_le m m') (h' := window_right_le m m')
    hx' hy (by omega)
  have hc : incR m m' y * incL m m' x' = (-1) ^ (k * k') * (incL m m' x' * incR m m' y) := by
    rw [incL, incR, hsc, ← mul_assoc, ← pow_add, mul_comm k' k, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_mul]
  simp only [tensorMap_tmul, map_mul]
  rw [mul_assoc, ← mul_assoc (incR m m' y), hc]
  simp only [mul_assoc, ((Commute.neg_one_left _).pow_left _).eq]

theorem homog_basis (i : (Fin (m+2) → ℕ) × Perm m) : ∃ k, Homog 0 (m+2) k (basis m i) := by
  obtain ⟨k, hk⟩ := homog_dotMonomial i.1
  rw [basis_apply, basisElement, dividedElement]
  exact ⟨_, hk.mul (homog_product (chosenWord i.2))⟩

/-- Induction over the PBW basis: a predicate closed under `0`, `+`, `ℤ`-multiples and holding
on homogeneous elements holds everywhere. -/
theorem induction_homog {p : Presented m → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : ℤ) x, p x → p (c • x)) (hhom : ∀ k x, Homog 0 (m+2) k x → p x)
    (x : Presented m) : p x := by
  have hx : x ∈ Submodule.span ℤ (Set.range (basis m)) := by rw [(basis m).span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨k, hk⟩ := homog_basis i
    exact hhom k _ hk
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul c y _ hy => exact hsmul c y hy

/-- The image of `ONH_a ⊗ ONH_b` in `ONH_{a+b}`: a subring, isomorphic to `ONH_a ⊗_ℤ ONH_b` as a
ℤ-module by `tensorMap` (`tensorMap_injective`), with multiplication given by the super tensor
product rule `tensorMap_mul`. -/
def tensorImage (m m' : ℕ) : Subring (Presented (m+2+m')) where
  carrier := Set.range (tensorMap m m')
  one_mem' := ⟨1 ⊗ₜ 1, tensorMap_one⟩
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, map_neg _ _⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    let R := LinearMap.range (tensorMap m m')
    have hsign : ∀ (j : ℕ) (z : Presented (m+2+m')), z ∈ R → (-1) ^ j * z ∈ R := by
      intro j z hz
      rcases neg_one_pow_eq_or (Presented (m+2+m')) j with h | h
      · rwa [h, one_mul]
      · rw [h, neg_one_mul]; exact R.neg_mem hz
    -- the product of two pure tensors lies in the image
    have key : ∀ (x : Presented m) (y : Presented m') (x' : Presented m) (y' : Presented m'),
        tensorMap m m' (x ⊗ₜ y) * tensorMap m m' (x' ⊗ₜ y') ∈ R := by
      intro x y x' y'
      induction y using induction_homog with
      | h0 => simp only [TensorProduct.tmul_zero, map_zero, zero_mul]; exact R.zero_mem
      | hadd y₁ y₂ h₁ h₂ =>
        simp only [TensorProduct.tmul_add, map_add, add_mul]; exact R.add_mem h₁ h₂
      | hsmul c y h =>
        simp only [TensorProduct.tmul_smul, map_zsmul, smul_mul_assoc]; exact R.smul_mem c h
      | hhom k y hy =>
        induction x' using induction_homog with
        | h0 => simp only [TensorProduct.zero_tmul, map_zero, mul_zero]; exact R.zero_mem
        | hadd x₁ x₂ h₁ h₂ =>
          simp only [TensorProduct.add_tmul, map_add, mul_add]; exact R.add_mem h₁ h₂
        | hsmul c x' h =>
          rw [← TensorProduct.smul_tmul', map_zsmul, mul_smul_comm]; exact R.smul_mem c h
        | hhom k' x' hx' =>
          rw [tensorMap_mul hy hx']
          exact hsign _ _ ⟨_, rfl⟩
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul]; exact R.zero_mem
    | add s₁ s₂ h₁ h₂ => simp only [map_add, add_mul]; exact R.add_mem h₁ h₂
    | tmul x y =>
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero, mul_zero]; exact R.zero_mem
      | add t₁ t₂ h₁ h₂ => simp only [map_add, mul_add]; exact R.add_mem h₁ h₂
      | tmul x' y' => exact key x y x' y'

theorem mem_tensorImage {z : Presented (m+2+m')} :
    z ∈ tensorImage m m' ↔ ∃ t, tensorMap m m' t = z := Iff.rfl

/-- `ONH_a ⊗_ℤ ONH_b ≃ tensorImage ⊂ ONH_{a+b}` as ℤ-modules. -/
def tensorEquiv (m m' : ℕ) : Presented m ⊗[ℤ] Presented m' ≃ₗ[ℤ] LinearMap.range (tensorMap m m') :=
  LinearEquiv.ofInjective (tensorMap m m') (tensorMap_injective m m')

theorem incL_mem_tensorImage (x : Presented m) : incL m m' x ∈ tensorImage m m' :=
  ⟨x ⊗ₜ 1, by rw [tensorMap_tmul, map_one, mul_one]⟩

theorem incR_mem_tensorImage (y : Presented m') : incR m m' y ∈ tensorImage m m' :=
  ⟨1 ⊗ₜ y, by rw [tensorMap_tmul, map_one, one_mul]⟩

end

end OddMath.Frontier.OnhStructure
