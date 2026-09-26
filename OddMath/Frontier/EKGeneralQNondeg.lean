import OddMath.Frontier.EKGeneralQCrossing
import OddMath.Frontier.EKGeneralQIdeal
import OddMath.Frontier.EKGeneralQTable
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Nondegeneracy of the q-form over `ℚ(q)`; degree and leading coefficient of the determinant

Source: Ellis–Khovanov, arXiv:1107.5610v2.

* §1.2, p.3: "`Λ'` ... has a natural bilinear form, which is nondegenerate over `ℚ(q)`."
* §5.2, p.40: "It is immediate from the definition of the bilinear form that this determinant
  is monic in `q`.  It is not hard to see that its degree is given by
  `D = Σ_α (½ n(n-1) - Σᵢ ½ αᵢ(αᵢ-1))`" (5.1), the sum over compositions `α` of `n`.

The Gram matrix of (2.1) on `Λ'ₙ` in the basis `h_α`, `α ⊨ n`, is `gram q n`.  Over `ℤ[q]`:

* `gram_det_natDegree`: `deg det = D` exactly as in (5.1);
* `gram_det_leadingCoeff`: the leading coefficient is the sign of the reversal `α ↦ α^rev` of
  compositions, a unit `±1` (so "monic" holds only up to this sign; it is `-1` for `n = 3`,
  `gram_det_three`, which refutes the printed claim);
* `gram_det_ne_zero`.

Consequently (`form_nondegenerate_of_det`) the form (2.1) is nondegenerate on all of `Λ'` over any
integral domain in which the specialised determinants are nonzero, in particular over `ℤ[q]` and
over `ℚ(q)` (`form_nondegenerate_ratFunc`), as claimed on p.3.

The degree bound comes from `EKGeneralQCrossing`: `2·crossing ≤ wt β + wt α` with equality only
for the antidiagonal matrix and `α = β^rev`, where `wt γ = C(|γ|,2) - Σ C(γᵢ,2)`.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKPairingMatrices Polynomial
open EKFreeCoproduct (W degree partWord partWord_degree)

/-! ## The weight `wt γ = C(|γ|,2) - Σ C(γᵢ,2)` -/

/-- Pairs of strands in different platforms: `C(|γ|,2) - Σᵢ C(γᵢ,2)` (the summand of (5.1)). -/
def wt (γ : List ℕ) : ℕ := γ.sum.choose 2 - (γ.map (fun a => a.choose 2)).sum

theorem two_mul_choose_two (m : ℕ) : 2 * ((m.choose 2 : ℕ) : ℤ) = (m : ℤ) ^ 2 - m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem two_mul_sum_choose_two (γ : List ℕ) :
    2 * (((γ.map (fun a => a.choose 2)).sum : ℕ) : ℤ) =
      (((γ.map (fun a => a ^ 2)).sum : ℕ) : ℤ) - (γ.sum : ℤ) := by
  induction γ with
  | nil => simp
  | cons a γ ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_pow]
    have := two_mul_choose_two a
    linear_combination this + ih

theorem sum_sq_le (γ : List ℕ) : (γ.map (fun a => a ^ 2)).sum ≤ γ.sum ^ 2 := by
  induction γ with
  | nil => simp
  | cons a γ ih =>
    simp only [List.map_cons, List.sum_cons]
    nlinarith [ih, Nat.zero_le (a * γ.sum)]

theorem two_mul_wt (γ : List ℕ) :
    2 * (wt γ : ℤ) = (γ.sum : ℤ) ^ 2 - (((γ.map (fun a => a ^ 2)).sum : ℕ) : ℤ) := by
  have h1 := two_mul_choose_two γ.sum
  have h2 := two_mul_sum_choose_two γ
  have hle : (γ.map (fun a => a.choose 2)).sum ≤ γ.sum.choose 2 := by
    have h3 := sum_sq_le γ
    have h3' : (((γ.map (fun a => a ^ 2)).sum : ℕ) : ℤ) ≤ (γ.sum : ℤ) ^ 2 := by exact_mod_cast h3
    have : (((γ.map (fun a => a.choose 2)).sum : ℕ) : ℤ) ≤ ((γ.sum.choose 2 : ℕ) : ℤ) := by
      linarith
    exact_mod_cast this
  unfold wt
  rw [Nat.cast_sub hle]
  linear_combination h1 - h2

theorem wt_reverse (γ : List ℕ) : wt γ.reverse = wt γ := by
  simp [wt, List.sum_reverse, List.map_reverse]

theorem sum_get_map (γ : List ℕ) (f : ℕ → ℤ) : (∑ i, f (γ.get i)) = (γ.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

theorem tPrime_get (γ : List ℕ) : tPrime γ.get = 2 * (wt γ : ℤ) := by
  rw [two_mul_wt, tPrime, sqSum]
  have h1 : (∑ i, γ.get i) = γ.sum := by rw [← List.sum_ofFn, List.ofFn_get]
  have h2 := sum_get_map γ (fun a => (a : ℤ) ^ 2)
  rw [h1, h2]
  push_cast
  simp [Function.comp_def]

/-! ## Entrywise bounds -/

theorem get_pos (β : Composition n) (i : Fin β.blocks.length) : 0 < β.blocks.get i :=
  β.blocks_pos (List.get_mem _ _)

theorem two_crossing_le (β α : Composition n) (M : Mat β.blocks.get α.blocks.get) :
    2 * crossing M.val ≤ wt β.blocks + wt α.blocks := by
  have h := four_crossing_le M
  rw [tPrime_get, tPrime_get] at h
  have : 4 * (crossing M.val : ℤ) ≤ 2 * (wt β.blocks : ℤ) + 2 * (wt α.blocks : ℤ) := h
  omega

theorem reverse_of_two_crossing_eq (β α : Composition n) (M : Mat β.blocks.get α.blocks.get)
    (he : 2 * crossing M.val = wt β.blocks + wt α.blocks) : α = β.reverse := by
  have hd : defect M.val = 0 := by
    apply (four_crossing_eq_iff M).mp
    rw [tPrime_get, tPrime_get]
    have : (2 * crossing M.val : ℤ) = (wt β.blocks : ℤ) + wt α.blocks := by exact_mod_cast he
    linarith
  obtain ⟨hrc, -, hα⟩ := eq_antidiag_of_defect_eq_zero M (get_pos β) (get_pos α) hd
  apply Composition.ext
  apply List.ext_getElem
  · simp [hrc]
  · intro j h1 h2
    simp only [Composition.reverse_blocks, List.getElem_reverse]
    have hj := hα ⟨j, h1⟩ ⟨β.blocks.length - 1 - j, by simp at h2; omega⟩
      (by simp at h2 ⊢; omega)
    simpa using hj

theorem exists_defect_zero {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) (h : r = c)
    (hα : ∀ (j : Fin c) (i : Fin r), j.val + i.val + 1 = r → α j = β i) :
    ∃ M : Mat β α, defect M.val = 0 := by
  subst h
  exact ⟨antidiagMat β α hα, defect_antidiag β⟩

/-- For `α = β^rev` exactly one margin matrix attains `2·crossing = wt β + wt α`. -/
theorem card_top_crossing (β : Composition n) :
    (Finset.univ.filter (fun M : Mat β.reverse.blocks.get β.blocks.get =>
      crossing M.val = wt β.blocks)).card = 1 := by
  classical
  have hw : wt β.reverse.blocks = wt β.blocks := by simp [wt_reverse]
  have key : ∀ M : Mat β.reverse.blocks.get β.blocks.get,
      crossing M.val = wt β.blocks ↔ defect M.val = 0 := by
    intro M
    rw [← four_crossing_eq_iff M, tPrime_get, tPrime_get, hw]
    constructor
    · intro h; rw [h]; ring
    · intro h
      have : (crossing M.val : ℤ) = wt β.blocks := by linarith
      exact_mod_cast this
  rw [Finset.card_eq_one]
  have hlen : β.reverse.blocks.length = β.blocks.length := by simp
  obtain ⟨M, hM⟩ := exists_defect_zero β.reverse.blocks.get β.blocks.get hlen (by
    intro j i hji
    simp only [List.get_eq_getElem, Composition.reverse_blocks, List.getElem_reverse]
    congr 1
    simp at hji ⊢
    omega)
  refine ⟨M, ?_⟩
  ext N
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, key]
  constructor
  · intro hN
    have h1 := (eq_antidiag_of_defect_eq_zero N (get_pos _) (get_pos _) hN).2.1
    have h2 := (eq_antidiag_of_defect_eq_zero M (get_pos _) (get_pos _) hM).2.1
    exact Subtype.ext (h1.trans h2.symm)
  · rintro rfl; exact hM

/-! ## The Gram matrix and its entries over `ℤ[q]` -/

variable {k : Type*} [CommRing k]

/-- The Gram matrix of (2.1) on `Λ'ₙ` in the basis `h_α`, `α ⊨ n`. -/
def gram (q : k) (n : ℕ) : Matrix (Composition n) (Composition n) k :=
  Matrix.of fun β α => form q (hWord k β.blocks) (hWord k α.blocks)

theorem gram_apply (q : k) (n : ℕ) (β α : Composition n) :
    gram q n β α = matForm q β.blocks.get α.blocks.get := by
  rw [gram, Matrix.of_apply, form_hWords, sourceFormAll_eq_matForm]

/-- Entries commute with ring homomorphisms. -/
theorem map_gram {S : Type*} [CommRing S] (φ : k →+* S) (q : k) (n : ℕ) :
    φ.mapMatrix (gram q n) = gram (φ q) n := by
  ext β α
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, gram_apply, matForm, map_sum, map_pow]

theorem natDegree_gram_le (β α : Composition n) :
    2 * (gram (X : ℤ[X]) n β α).natDegree + (if α = β.reverse then 0 else 1) ≤
      wt β.blocks + wt α.blocks := by
  have hb : ∀ M : Mat β.blocks.get α.blocks.get,
      2 * crossing M.val + (if α = β.reverse then 0 else 1) ≤ wt β.blocks + wt α.blocks := by
    intro M
    have h := two_crossing_le β α M
    split_ifs with he
    · simpa using h
    · have hne : 2 * crossing M.val ≠ wt β.blocks + wt α.blocks :=
        fun h' => he (reverse_of_two_crossing_eq β α M h')
      omega
  obtain ⟨M₀⟩ : Nonempty (Mat β.blocks.get α.blocks.get) := by
    have hs : (∑ i, β.blocks.get i) = ∑ j, α.blocks.get j := by
      rw [← List.sum_ofFn, List.ofFn_get, ← List.sum_ofFn, List.ofFn_get, β.blocks_sum,
        α.blocks_sum]
    exact ⟨EKPlatformBijection.doubleCosetEquiv _ _ hs (Quotient.mk _ 1)⟩
  have h0 := hb M₀
  have hd : (gram (X : ℤ[X]) n β α).natDegree ≤
      (wt β.blocks + wt α.blocks - (if α = β.reverse then 0 else 1)) / 2 := by
    rw [gram_apply, matForm]
    apply natDegree_sum_le_of_forall_le
    intro M _
    rw [natDegree_X_pow]
    have := hb M
    omega
  omega

theorem coeff_gram (β α : Composition n) (e : ℕ) :
    (gram (X : ℤ[X]) n β α).coeff e =
      (Finset.univ.filter (fun M : Mat β.blocks.get α.blocks.get => crossing M.val = e)).card := by
  classical
  rw [gram_apply, matForm, finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro M _
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem gram_reverse_monic (β : Composition n) :
    (gram (X : ℤ[X]) n β.reverse β).Monic ∧
      (gram (X : ℤ[X]) n β.reverse β).natDegree = wt β.blocks := by
  have hle := natDegree_gram_le β.reverse β
  rw [if_pos (Composition.reverse_reverse β).symm, Composition.reverse_blocks, wt_reverse] at hle
  have hle' : (gram (X : ℤ[X]) n β.reverse β).natDegree ≤ wt β.blocks := by omega
  have hc : (gram (X : ℤ[X]) n β.reverse β).coeff (wt β.blocks) = 1 := by
    rw [coeff_gram, card_top_crossing]
    rfl
  have hdeg : (gram (X : ℤ[X]) n β.reverse β).natDegree = wt β.blocks :=
    le_antisymm hle' (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, hdeg, hc], hdeg⟩

/-! ## The determinant over `ℤ[q]` -/

/-- The reversal `α ↦ α^rev` of compositions of `n`. -/
def revPerm (n : ℕ) : Equiv.Perm (Composition n) :=
  Function.Involutive.toPerm _ Composition.reverse_involutive

@[simp] theorem revPerm_apply (β : Composition n) : revPerm n β = β.reverse := rfl

/-- EK (5.1): `D = Σ_{α ⊨ n} (C(n,2) - Σᵢ C(αᵢ,2))`. -/
def degD (n : ℕ) : ℕ := ∑ α : Composition n, (n.choose 2 - (α.blocks.map (fun a => a.choose 2)).sum)

theorem degD_eq (n : ℕ) : degD n = ∑ α : Composition n, wt α.blocks := by
  unfold degD wt
  apply Finset.sum_congr rfl
  intro α _
  rw [α.blocks_sum]

theorem natDegree_term_lt (σ : Equiv.Perm (Composition n)) (hσ : σ ≠ revPerm n) :
    (∏ i, gram (X : ℤ[X]) n (σ i) i).natDegree < degD n := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ revPerm n i := by
    by_contra h
    push_neg at h
    exact hσ (Equiv.ext h)
  have hsum : 2 * (∑ i, (gram (X : ℤ[X]) n (σ i) i).natDegree) + 1 ≤ 2 * degD n := by
    have hb : ∀ i, 2 * (gram (X : ℤ[X]) n (σ i) i).natDegree +
        (if i = (σ i).reverse then 0 else 1) ≤ wt (σ i).blocks + wt i.blocks :=
      fun i => natDegree_gram_le (σ i) i
    have h1 : ∑ i, (2 * (gram (X : ℤ[X]) n (σ i) i).natDegree +
        (if i = (σ i).reverse then 0 else 1)) ≤ ∑ i, (wt (σ i).blocks + wt i.blocks) :=
      Finset.sum_le_sum (fun i _ => hb i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Equiv.sum_comp σ (fun i => wt i.blocks)] at h1
    have h2 : 1 ≤ ∑ i, (if i = (σ i).reverse then 0 else 1) := by
      have : (if i₀ = (σ i₀).reverse then 0 else 1) = 1 := by
        rw [if_neg]
        intro h
        apply hi₀
        have h' := congrArg Composition.reverse h
        rw [Composition.reverse_reverse] at h'
        rw [revPerm_apply, h']
      calc 1 = (if i₀ = (σ i₀).reverse then 0 else 1) := this.symm
        _ ≤ _ := Finset.single_le_sum (f := fun i => if i = (σ i).reverse then 0 else 1)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
    rw [degD_eq]
    omega
  calc (∏ i, gram (X : ℤ[X]) n (σ i) i).natDegree
      ≤ ∑ i, (gram (X : ℤ[X]) n (σ i) i).natDegree := natDegree_prod_le _ _
    _ < degD n := by omega

theorem term_rev_monic :
    (∏ i, gram (X : ℤ[X]) n (revPerm n i) i).Monic ∧
      (∏ i, gram (X : ℤ[X]) n (revPerm n i) i).natDegree = degD n := by
  have hm : ∀ i ∈ (Finset.univ : Finset (Composition n)),
      (gram (X : ℤ[X]) n (revPerm n i) i).Monic :=
    fun i _ => (gram_reverse_monic i).1
  refine ⟨monic_prod_of_monic _ _ hm, ?_⟩
  rw [natDegree_prod_of_monic _ _ hm, degD_eq]
  exact Finset.sum_congr rfl (fun i _ => (gram_reverse_monic i).2)

theorem coeff_gram_det (m : ℕ) (hm : degD n ≤ m) :
    (gram (X : ℤ[X]) n).det.coeff m =
      (Equiv.Perm.sign (revPerm n) : ℤ) * (∏ i, gram (X : ℤ[X]) n (revPerm n i) i).coeff m := by
  rw [Matrix.det_apply', finset_sum_coeff, Finset.sum_eq_single (revPerm n)]
  · rw [coeff_intCast_mul, Int.cast_id]
  · intro σ _ hσ
    rw [coeff_intCast_mul, coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le
      (natDegree_term_lt σ hσ) hm), mul_zero]
  · simp

/-- EK (5.1): the Gram determinant of `Λ'ₙ` over `ℤ[q]` has degree `D`. -/
theorem gram_det_natDegree (n : ℕ) : (gram (X : ℤ[X]) n).det.natDegree = degD n := by
  have htop := term_rev_monic (n := n)
  have hD : (gram (X : ℤ[X]) n).det.coeff (degD n) = (Equiv.Perm.sign (revPerm n) : ℤ) := by
    rw [coeff_gram_det _ le_rfl, ← htop.2, htop.1.coeff_natDegree, mul_one]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm' : degD n < m := by exact_mod_cast hm
    rw [coeff_gram_det _ (le_of_lt hm'), coeff_eq_zero_of_natDegree_lt (htop.2 ▸ hm'), mul_zero]
  · apply le_natDegree_of_ne_zero
    rw [hD]
    exact Units.ne_zero _

/-- EK §5.2 p.40, corrected: the leading coefficient of the Gram determinant is the sign of the
reversal of compositions (a unit `±1`), not always `1`. -/
theorem gram_det_leadingCoeff (n : ℕ) :
    (gram (X : ℤ[X]) n).det.leadingCoeff = (Equiv.Perm.sign (revPerm n) : ℤ) := by
  have htop := term_rev_monic (n := n)
  rw [leadingCoeff, gram_det_natDegree, coeff_gram_det _ le_rfl, ← htop.2,
    htop.1.coeff_natDegree, mul_one]

theorem gram_det_leadingCoeff_isUnit (n : ℕ) : IsUnit (gram (X : ℤ[X]) n).det.leadingCoeff := by
  rw [gram_det_leadingCoeff]
  exact (Equiv.Perm.sign (revPerm n)).isUnit.map (Int.castRingHom ℤ)

/-- The Gram determinant of `Λ'ₙ` over `ℤ[q]` is nonzero, for every `n`. -/
theorem gram_det_ne_zero (n : ℕ) : (gram (X : ℤ[X]) n).det ≠ 0 := by
  intro h
  have := gram_det_leadingCoeff n
  rw [h, leadingCoeff_zero] at this
  exact Units.ne_zero _ this.symm

/-! ## Degree 3: the canonical determinant and the sign of the reversal -/

/-- The printed degree-3 compositions as elements of `Composition 3`. -/
def comp3 (i : Fin 4) : Composition 3 where
  blocks := comps3 i
  blocks_pos := by intro a ha; fin_cases i <;> simp [comps3] at ha <;> omega
  blocks_sum := by fin_cases i <;> rfl

theorem comp3_bijective : Function.Bijective comp3 := by
  rw [Fintype.bijective_iff_injective_and_card, Fintype.card_fin, composition_card]
  refine ⟨?_, rfl⟩
  intro i j h
  have h' : comps3 i = comps3 j := congrArg Composition.blocks h
  fin_cases i <;> fin_cases j <;> simp_all [comps3]

/-- The printed order of the degree-3 compositions. -/
def comp3Equiv : Fin 4 ≃ Composition 3 := Equiv.ofBijective comp3 comp3_bijective

theorem gram_det_three_eq (q : k) : (gram q 3).det = (gramPrinted q comps3).det := by
  rw [← Matrix.det_submatrix_equiv_self comp3Equiv (gram q 3)]
  congr 1

/-- EK §5.2: over `ℤ[q]` the degree-3 determinant is `-q⁵(q-1)(q+1)`; its leading coefficient
`-1` is the sign of the reversal of compositions of `3` (one transposition `12 ↔ 21`). -/
theorem gram_det_three :
    (gram (X : ℤ[X]) 3).det = -(X ^ 5 * (X - 1) * (X + 1)) ∧
      (Equiv.Perm.sign (revPerm 3) : ℤ) = -1 := by
  have h := det_gram3_not_monic
  rw [← gram_det_three_eq] at h
  exact ⟨h.1, (gram_det_leadingCoeff 3).symm.trans h.2.2.1⟩

/-! ## Words of degree `n` and compositions of `n` -/

theorem toList_partWord (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    (partWord l).toList.map (· + 1) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by have := hl a (by simp); omega⟩
    simp only [partWord, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.map_cons, List.cons.injEq, true_and]
    exact ih (fun b hb => hl b (by simp [hb]))

theorem partWord_toList (w : W) : partWord (w.toList.map (· + 1)) = w := by
  induction w using FreeMonoid.recOn with
  | h0 => rfl
  | ih i w ih =>
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.map_cons, partWord, ih]

/-- Compositions of `n` are the words of degree `n` (`α ↦ h_α`). -/
def wordEquiv (n : ℕ) : Composition n ≃ {w : W // degree w = n} where
  toFun β := ⟨partWord β.blocks, by rw [partWord_degree, β.blocks_sum]⟩
  invFun w :=
    { blocks := w.1.toList.map (· + 1)
      blocks_pos := by intro a ha; simp only [List.mem_map] at ha; omega
      blocks_sum := w.2 }
  left_inv β := Composition.ext (toList_partWord _ (fun a ha => β.blocks_pos ha))
  right_inv w := Subtype.ext (partWord_toList w.1)

instance (n : ℕ) : Fintype {w : W // degree w = n} := Fintype.ofEquiv _ (wordEquiv n)

theorem hWord_blocks (β : Composition n) :
    hWord k β.blocks = wordBasis k (partWord β.blocks) := (partWord_value k _).symm

theorem degreeProj_eq_sum (n : ℕ) (x : L k) :
    degreeProj k n x =
      ∑ β : Composition n, (wordBasis k).repr x (partWord β.blocks) • hWord k β.blocks := by
  classical
  simp only [hWord_blocks]
  rw [Fintype.sum_equiv (wordEquiv n)
    (fun β : Composition n => (wordBasis k).repr x (partWord β.blocks) •
      wordBasis k (partWord β.blocks))
    (fun w : {w : W // degree w = n} => (wordBasis k).repr x w.1 • wordBasis k w.1)
    (fun β => rfl)]
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib, hx, hy]
  | hb u r =>
    simp only [map_smul, degreeProj_basis, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    by_cases hu : degree u = n
    · rw [if_pos hu, Finset.sum_eq_single ⟨u, hu⟩]
      · simp
      · intro w _ hw
        rw [if_neg]
        intro h
        exact hw (Subtype.ext h.symm)
      · simp
    · rw [if_neg hu, smul_zero]
      symm
      apply Finset.sum_eq_zero
      intro w _
      rw [if_neg]
      intro h
      exact hu (h ▸ w.2)

/-! ## Nondegeneracy -/

/-- If every Gram determinant is nonzero in the integral domain `k`, the form (2.1) is
nondegenerate on `Λ'`. -/
theorem form_nondegenerate_of_det [IsDomain k] (q : k) (hdet : ∀ n, (gram q n).det ≠ 0)
    (x : L k) (hx : ∀ y, form q x y = 0) : x = 0 := by
  classical
  apply (wordBasis k).repr.injective
  ext w
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  set n := degree w
  let v : Composition n → k := fun β => (wordBasis k).repr x (partWord β.blocks)
  have hv : Matrix.vecMul v (gram q n) = 0 := by
    funext α
    have h1 : (Matrix.vecMul v (gram q n)) α = form q (degreeProj k n x) (hWord k α.blocks) := by
      rw [degreeProj_eq_sum, map_sum, LinearMap.sum_apply]
      simp only [Matrix.vecMul, dotProduct, map_smul, LinearMap.smul_apply, smul_eq_mul, v, gram,
        Matrix.of_apply]
    have h2 : degreeProj k n (hWord k α.blocks) = hWord k α.blocks := by
      rw [hWord_blocks, degreeProj_basis, if_pos (by rw [partWord_degree, α.blocks_sum])]
    rw [h1, form_degreeProj, h2, hx]
    rfl
  have hv0 : v = 0 := by
    rcases eq_or_ne v 0 with h | hne
    · exact h
    · exact absurd (Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hne, hv⟩) (hdet n)
  have := congrFun hv0 ((wordEquiv n).symm ⟨w, rfl⟩)
  have hw : partWord ((wordEquiv n).symm ⟨w, rfl⟩).blocks = w :=
    congrArg Subtype.val ((wordEquiv n).apply_symm_apply ⟨w, rfl⟩)
  simpa [v, hw] using this

/-- The form (2.1) is nondegenerate over `ℤ[q]`. -/
theorem form_nondegenerate_polynomial (x : L ℤ[X]) (hx : ∀ y, form (X : ℤ[X]) x y = 0) :
    x = 0 :=
  form_nondegenerate_of_det X gram_det_ne_zero x hx

/-- `ℤ[q] → ℚ(q)`. -/
def toRatFunc : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem toRatFunc_injective : Function.Injective toRatFunc :=
  (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

theorem toRatFunc_X : toRatFunc X = RatFunc.X := by
  simp [toRatFunc, RatFunc.algebraMap_X]

theorem gram_det_ratFunc_ne_zero (n : ℕ) : (gram (RatFunc.X : RatFunc ℚ) n).det ≠ 0 := by
  rw [← toRatFunc_X, ← map_gram, ← RingHom.map_det]
  exact (map_ne_zero_iff _ toRatFunc_injective).mpr (gram_det_ne_zero n)

/-- EK §1.2 p.3: the form on `Λ'` is nondegenerate over `ℚ(q)`. -/
theorem form_nondegenerate_ratFunc (x : L (RatFunc ℚ))
    (hx : ∀ y, form (RatFunc.X : RatFunc ℚ) x y = 0) : x = 0 :=
  form_nondegenerate_of_det _ gram_det_ratFunc_ne_zero x hx

/-- Summary: EK §1.2 nondegeneracy over `ℚ(q)` and the corrected §5.2 determinant data. -/
theorem ek_nondegenerate_general_q :
    (∀ x : L (RatFunc ℚ), (∀ y, form (RatFunc.X : RatFunc ℚ) x y = 0) → x = 0) ∧
    (∀ n, (gram (X : ℤ[X]) n).det ≠ 0 ∧
      (gram (X : ℤ[X]) n).det.natDegree = degD n ∧
      (gram (X : ℤ[X]) n).det.leadingCoeff = (Equiv.Perm.sign (revPerm n) : ℤ)) ∧
    (gram (X : ℤ[X]) 3).det.leadingCoeff = -1 :=
  ⟨form_nondegenerate_ratFunc, fun n => ⟨gram_det_ne_zero n, gram_det_natDegree n,
    gram_det_leadingCoeff n⟩, (gram_det_leadingCoeff 3).trans gram_det_three.2⟩

end OddMath.Frontier.EKGeneralQ
