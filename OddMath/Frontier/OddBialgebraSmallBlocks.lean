import OddMath.Frontier.OddBialgebraSmallCorner

/-!
# Windows of size one: permutations and PBW monomials

EKL arXiv:1111.1320v1, §6, pp. 46–47. The Young subgroups `S_1 × S_b ⊂ S_{1+b}` and
`S_a × S_1 ⊂ S_{a+1}`, and the images of the PBW monomials under the embeddings of a window of
size `1` (`dotHom`) next to a window of size `b ≥ 2` (`OnhWindow.windowHom`).

* `shiftR v = 1 × v ∈ S_{1+b}` (`b = m'+2`), `shiftL v = v × 1 ∈ S_{a+1}` (`a = m+2`); both preserve
  lengths and are the Young subgroups (`young_shiftR`, `young_shiftL`); the window embeddings
  carry `∂_v` to `± ∂_{1 × v}`, `± ∂_{v × 1}`.
* `dotHom_mul_windowHom_dotMonomial`, `windowHom_dotMonomial_mul_dotHom`: products of dot
  monomials in adjacent windows are the concatenated monomials.
-/

noncomputable section

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords NilHeckeAction NilHeckeBasis OnhWindow OnhStructure
open OddMath.SkewPolynomial (SkewPolynomial)

/-! ### Young subgroups as products -/

theorem exists_sumCongr_of_young {P Q : ℕ} (y : Equiv.Perm (Fin (P + Q)))
    (hy : ∀ x : Fin (P + Q), ((y x : ℕ) < P ↔ (x : ℕ) < P)) :
    ∃ a b, y = (finSumFinEquiv (m := P) (n := Q)).permCongr (Equiv.Perm.sumCongr a b) := by
  let σ := (finSumFinEquiv (m := P) (n := Q)).symm.permCongr y
  have hσ : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨a, rfl⟩
    have h : ((y (Fin.castAdd Q a) : Fin (P + Q)) : ℕ) < P := (hy _).2 (by simp)
    refine ⟨⟨_, h⟩, ?_⟩
    show _ = finSumFinEquiv.symm (y (finSumFinEquiv.symm.symm (Sum.inl a)))
    rw [Equiv.symm_symm, finSumFinEquiv_apply_left]
    have e : y (Fin.castAdd Q a) = Fin.castAdd Q ⟨_, h⟩ := Fin.ext rfl
    exact (finSumFinEquiv_symm_apply_castAdd _).symm.trans (congrArg _ e.symm)
  obtain ⟨⟨a, b⟩, hab⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσ
  refine ⟨a, b, ?_⟩
  rw [Equiv.Perm.sumCongrHom_apply] at hab
  rw [hab]
  ext x
  simp [σ, Equiv.permCongr_apply]

/-! ### The window `{0}` next to `[1, b+1)` -/

section Right

variable {m' : ℕ}

theorem hR (m' : ℕ) : 1 + (m'+2) ≤ (1 + m') + 2 := by omega

/-- `1 × v ∈ S_{1+b}`. -/
def shiftR (v : Perm m') : Perm (1 + m') :=
  (finSumFinEquiv (m := 1) (n := m'+2)).permCongr (Equiv.Perm.sumCongr 1 v)

@[simp] theorem shiftR_castAdd (v : Perm m') (i : Fin 1) :
    shiftR v (Fin.castAdd (m'+2) i) = Fin.castAdd (m'+2) i := by
  show (finSumFinEquiv (m := 1) (n := m'+2)) (Equiv.Perm.sumCongr 1 v
    ((finSumFinEquiv (m := 1) (n := m'+2)).symm (Fin.castAdd (m'+2) i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]
  rfl

@[simp] theorem shiftR_natAdd (v : Perm m') (j : Fin (m'+2)) :
    shiftR v (Fin.natAdd 1 j) = Fin.natAdd 1 (v j) := by
  show (finSumFinEquiv (m := 1) (n := m'+2)) (Equiv.Perm.sumCongr 1 v
    ((finSumFinEquiv (m := 1) (n := m'+2)).symm (Fin.natAdd 1 j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem shiftR_mul (v v' : Perm m') : shiftR (v * v') = shiftR v * shiftR v' := by
  simp only [shiftR]
  rw [show (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) (v * v')) =
    Equiv.Perm.sumCongr 1 v * Equiv.Perm.sumCongr 1 v' by rw [Equiv.Perm.sumCongr_mul, one_mul]]
  exact Equiv.ext fun x => by simp [Equiv.Perm.mul_apply]

theorem shiftR_one : shiftR (1 : Perm m') = 1 := by
  simp only [shiftR, Equiv.Perm.sumCongr_one]
  exact Equiv.ext fun x => by simp

theorem simple_shiftR1 (i : Fin (m'+1)) :
    simple (shiftIndex (hR m') i) = shiftR (simple i) := by
  rw [shiftR, simple, simple, Equiv.Perm.sumCongr_one_swap, Equiv.permCongr_def,
    Equiv.symm_trans_swap_trans, finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]
  congr 1 <;> exact Fin.ext (by
    simp only [Fin.coe_castSucc, Fin.val_succ, Fin.coe_natAdd, shiftIndex_val]; omega)

theorem permutation_mapR1 (u : Word m') :
    permutation (u.map (shiftIndex (hR m'))) = shiftR (permutation u) := by
  induction u with
  | nil => exact shiftR_one.symm
  | cons i u ih => rw [List.map_cons, permutation, permutation, ih, simple_shiftR1, shiftR_mul]

theorem length_shiftR (v : Perm m') : length (shiftR v) = length v := by
  change (∑ a : Fin (1 + (m'+2)), ∑ b : Fin (1 + (m'+2)),
    if a < b ∧ shiftR v b < shiftR v a then 1 else 0) = _
  simp only [Fin.sum_univ_add (a := 1) (b := m'+2), shiftR_castAdd, shiftR_natAdd,
    Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  have h₁ : ∀ (i : Fin 1) (j : Fin (m'+2)),
      (if (i : ℕ) < 1 + j ∧ 1 + (v j : ℕ) < i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := i.isLt; omega
  have h₂ : ∀ (i : Fin (m'+2)) (j : Fin 1),
      (if 1 + (i : ℕ) < j ∧ (j : ℕ) < 1 + v i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := j.isLt; omega
  have h₀ : ∀ (i j : Fin 1), (if (i : ℕ) < j ∧ (j : ℕ) < i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by omega
  simp only [h₀, h₁, h₂, Finset.sum_const_zero, add_zero, zero_add, length,
    Fin.lt_iff_val_lt_val]

theorem windowHom_dividedR (v : Perm m') :
    Signed (windowHom m' (1 + m') 1 (hR m') (dividedElement v)) (dividedElement (shiftR v)) := by
  rw [dividedElement, windowHom_product]
  have hp : permutation ((chosenWord v).map (shiftIndex (hR m'))) = shiftR v := by
    rw [permutation_mapR1, chosenWord_permutation]
  have hr : Reduced ((chosenWord v).map (shiftIndex (hR m'))) := by
    unfold Reduced
    rw [hp, length_shiftR, List.length_map, chosenWord_length]
  have := reduced_dividedElement _ hr
  rwa [hp] at this

theorem isYoung_shiftR (v : Perm m') : IsYoung 1 (shiftR v) := by
  intro x
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ : (∃ k : Fin 1, x = Fin.castAdd (m'+2) k) ∨
      ∃ k : Fin (m'+2), x = Fin.natAdd 1 k := by
    by_cases h : (x : ℕ) < 1
    · exact Or.inl ⟨⟨x, h⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨x - 1, by omega⟩, Fin.ext (by simp; omega)⟩
  · rw [shiftR_castAdd]
  · rw [shiftR_natAdd]
    simp [InBlk]

theorem young_shiftR {y : Perm (1 + m')} (hy : IsYoung 1 y) : ∃ v, y = shiftR v := by
  obtain ⟨a, b, h⟩ := exists_sumCongr_of_young (P := 1) (Q := m'+2) y hy
  obtain rfl : a = 1 := Subsingleton.elim _ _
  exact ⟨b, h⟩

theorem dotHom_mul_windowHom_dotMonomial (a : Fin 1 → ℕ) (A : Fin (m'+2) → ℕ) :
    dotHom (1 + m') 0 (Finsupp.single a 1) * windowHom m' (1 + m') 1 (hR m') (dotMonomial A) =
      dotMonomial (Fin.append a A : Fin (1 + (m'+2)) → ℕ) := by
  rw [dotHom_single, one_smul, dotMonomial_eq_prod_ofFn, dotMonomial_eq_prod_ofFn,
    List.ofFn_add (m := 1) (n := m'+2), List.prod_append, map_list_prod, List.map_ofFn]
  congr 1
  · rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    simp only [Fin.append_left]
    rfl
  · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    simp only [Function.comp_apply, map_pow, windowHom_dot, Fin.append_right]
    congr 2
    exact Fin.ext (by simp [add_comm])

end Right

/-! ### The window `[0, a)` next to `{a}` -/

section Left

variable {m : ℕ}

theorem hL (m : ℕ) : 0 + (m+2) ≤ (m+1) + 2 := by omega

/-- `v × 1 ∈ S_{a+1}`. -/
def shiftL (v : Perm m) : Perm (m+1) :=
  (finSumFinEquiv (m := m+2) (n := 1)).permCongr (Equiv.Perm.sumCongr v 1)

@[simp] theorem shiftL_castAdd (v : Perm m) (i : Fin (m+2)) :
    shiftL v (Fin.castAdd 1 i) = Fin.castAdd 1 (v i) := by
  show (finSumFinEquiv (m := m+2) (n := 1)) (Equiv.Perm.sumCongr v 1
    ((finSumFinEquiv (m := m+2) (n := 1)).symm (Fin.castAdd 1 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

@[simp] theorem shiftL_natAdd (v : Perm m) (j : Fin 1) :
    shiftL v (Fin.natAdd (m+2) j) = Fin.natAdd (m+2) j := by
  show (finSumFinEquiv (m := m+2) (n := 1)) (Equiv.Perm.sumCongr v 1
    ((finSumFinEquiv (m := m+2) (n := 1)).symm (Fin.natAdd (m+2) j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]
  rfl

theorem shiftL_mul (v v' : Perm m) : shiftL (v * v') = shiftL v * shiftL v' := by
  simp only [shiftL]
  rw [show (Equiv.Perm.sumCongr (v * v') (1 : Equiv.Perm (Fin 1))) =
    Equiv.Perm.sumCongr v 1 * Equiv.Perm.sumCongr v' 1 by rw [Equiv.Perm.sumCongr_mul, one_mul]]
  exact Equiv.ext fun x => by simp [Equiv.Perm.mul_apply]

theorem shiftL_one : shiftL (1 : Perm m) = 1 := by
  simp only [shiftL, Equiv.Perm.sumCongr_one]
  exact Equiv.ext fun x => by simp

theorem simple_shiftL1 (i : Fin (m+1)) :
    simple (shiftIndex (hL m) i) = shiftL (simple i) := by
  rw [shiftL, simple, simple, Equiv.Perm.sumCongr_swap_one, Equiv.permCongr_def,
    Equiv.symm_trans_swap_trans, finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
  congr 1

theorem permutation_mapL1 (u : Word m) :
    permutation (u.map (shiftIndex (hL m))) = shiftL (permutation u) := by
  induction u with
  | nil => exact shiftL_one.symm
  | cons i u ih => rw [List.map_cons, permutation, permutation, ih, simple_shiftL1, shiftL_mul]

theorem length_shiftL (v : Perm m) : length (shiftL v) = length v := by
  change (∑ a : Fin ((m+2) + 1), ∑ b : Fin ((m+2) + 1),
    if a < b ∧ shiftL v b < shiftL v a then 1 else 0) = _
  simp only [Fin.sum_univ_add (a := m+2) (b := 1), shiftL_castAdd, shiftL_natAdd,
    Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  have h₁ : ∀ (i : Fin (m+2)) (j : Fin 1),
      (if (i : ℕ) < m+2+j ∧ m+2+(j : ℕ) < v i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := (v i).isLt; omega
  have h₂ : ∀ (i : Fin 1) (j : Fin (m+2)),
      (if m+2+(i : ℕ) < j ∧ (v j : ℕ) < m+2+i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by have := j.isLt; omega
  have h₀ : ∀ (i j : Fin 1), (if (i : ℕ) < j ∧ (j : ℕ) < i then 1 else 0) = 0 := fun i j =>
    if_neg fun h => by omega
  simp only [h₀, h₁, h₂, Finset.sum_const_zero, add_zero, length, Fin.lt_iff_val_lt_val]

theorem windowHom_dividedL (v : Perm m) :
    Signed (windowHom m (m+1) 0 (hL m) (dividedElement v)) (dividedElement (shiftL v)) := by
  rw [dividedElement, windowHom_product]
  have hp : permutation ((chosenWord v).map (shiftIndex (hL m))) = shiftL v := by
    rw [permutation_mapL1, chosenWord_permutation]
  have hr : Reduced ((chosenWord v).map (shiftIndex (hL m))) := by
    unfold Reduced
    rw [hp, length_shiftL, List.length_map, chosenWord_length]
  have := reduced_dividedElement _ hr
  rwa [hp] at this

theorem isYoung_shiftL (v : Perm m) : IsYoung (m+2) (shiftL v) := by
  intro x
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ : (∃ k : Fin (m+2), x = Fin.castAdd 1 k) ∨
      ∃ k : Fin 1, x = Fin.natAdd (m+2) k := by
    by_cases h : (x : ℕ) < m+2
    · exact Or.inl ⟨⟨x, h⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨x - (m+2), by omega⟩, Fin.ext (by simp; omega)⟩
  · rw [shiftL_castAdd]
    simp [InBlk]
  · rw [shiftL_natAdd]

theorem young_shiftL {y : Perm (m+1)} (hy : IsYoung (m+2) y) : ∃ v, y = shiftL v := by
  obtain ⟨a, b, h⟩ := exists_sumCongr_of_young (P := m+2) (Q := 1) y hy
  obtain rfl : b = 1 := Subsingleton.elim _ _
  exact ⟨a, h⟩

/-- The last strand of `ONH_{a+1}`. -/
def lastFin (m : ℕ) : Fin (m+1+2) := ⟨m+2, by omega⟩

theorem windowHom_dotMonomial_mul_dotHom (A : Fin (m+2) → ℕ) (b : Fin 1 → ℕ) :
    windowHom m (m+1) 0 (hL m) (dotMonomial A) * dotHom (m+1) (lastFin m) (Finsupp.single b 1) =
      dotMonomial (Fin.append A b : Fin ((m+2) + 1) → ℕ) := by
  rw [dotHom_single, one_smul, dotMonomial_eq_prod_ofFn, dotMonomial_eq_prod_ofFn,
    List.ofFn_add (m := m+2) (n := 1), List.prod_append, map_list_prod, List.map_ofFn]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    simp only [Function.comp_apply, map_pow, windowHom_dot, Fin.append_left]
    congr 2
  · rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    simp only [Fin.append_right]
    congr 2

theorem windowHom_divided_mul_dot_pow (v : Perm m) (k : ℕ) :
    Signed (windowHom m (m+1) 0 (hL m) (dividedElement v) * dot (m+1) (lastFin m) ^ k)
      (dot (m+1) (lastFin m) ^ k * windowHom m (m+1) 0 (hL m) (dividedElement v)) := by
  have hu : Homog 0 (m+2) (chosenWord v).length
      (windowHom m (m+1) 0 (hL m) (dividedElement v)) :=
    (homog_product (chosenWord v)).windowHom (n := m+1) (p := 0) (h := hL m)
  have hv : Homog (m+2) (m+3) k (dot (m+1) (lastFin m) ^ k) := by
    rw [dot_pow_eq]
    have := homog_wordValue (l := m+2) (r := m+3)
      (List.replicate k (Sum.inl (lastFin m) : NilHeckeGrading.Letter (m+1))) (fun g hg => by
        rw [List.eq_of_mem_replicate hg]
        exact ⟨le_rfl, by simp [lastFin]⟩)
    rwa [List.length_replicate] at this
  rw [hu.supercomm hv le_rfl]
  exact signed_neg_one_pow_mul _ _

end Left

end OddMath.Frontier.OddBialgebra
