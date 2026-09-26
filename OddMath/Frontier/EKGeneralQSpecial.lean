import OddMath.Frontier.EKGeneralQIdeal

/-!
# EK §2.1 at the special values q = 0 and q = 1, and cocommutativity

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, pp.5 and 8–9.

* p.5: "The q-bialgebra `Λ'` is cocommutative if and only if `q = 1`." (`cocommutative_iff`,
  any commutative ring `k`, any `q : k`.)
* p.8: "If `q = 0`, the bilinear form degenerates and `dim(Λₙ) = 1` for all `n ≥ 0`."
  (`form_zero_hWords`: at `q = 0` every Gram entry of equal degree is `1`, since exactly one
  double coset has a minimal representative of length `0`; `degreePiece0_finrank`: the degree-`n`
  part of `Λ₀` is free of rank `1` over any nontrivial `k`, with basis `hₙ`;
  `form_zero_degenerate`.)
* p.8: "If `q = 1`, the inner product `(h_β, h_α) = |βS_α|` is the number of double cosets"
  (`form_one_hWords`), equal to the number of `ℕ`-matrices with row sums `β` and column sums `α`
  (`form_one_hWords_mat`), the classical value of `⟨h_β, h_α⟩`.  The commutators
  `[hₙ, hₘ]` (indeed all `xy - yx`) lie in the radical `I₁` (`commutator_mem_radical_one`),
  so `Λ₁` is commutative (`lam_one_mul_comm`).
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree degree_one degree_mul)
open EKPlatformBijection (DoubleCosets endpoint endpoint_monotone cosetLength inversions
  SameDoubleCoset IsMinimal minimalRepresentative minimalRepresentative_spec)

variable {k : Type*} [CommRing k]

/-! ## Double cosets of length zero -/

theorem inversions_one {n : ℕ} : inversions (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold inversions
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact absurd (lt_trans h1 h2) (lt_irrefl a)

theorem eq_one_of_inversions_eq_zero {n : ℕ} (σ : Equiv.Perm (Fin n))
    (h : inversions σ = 0) : σ = 1 := by
  have hmono : StrictMono σ := by
    intro a b hab
    have hz := (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
    have hz' := (Finset.sum_eq_zero_iff.mp hz) b (Finset.mem_univ b)
    by_contra hn
    have hne : σ a ≠ σ b := fun he => (ne_of_lt hab) (σ.injective he)
    have hlt : σ b < σ a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
    rw [if_pos ⟨hab, hlt⟩] at hz'
    exact one_ne_zero hz'
  let e : Fin n ≃o Fin n := StrictMono.orderIsoOfSurjective σ hmono σ.surjective
  have he : e = OrderIso.refl (Fin n) := Subsingleton.elim _ _
  apply Equiv.ext
  intro a
  have := congrArg (fun f : Fin n ≃o Fin n => (f a : Fin n)) he
  simpa [e] using this

theorem cosetLength_eq_zero_iff {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) (x : DoubleCosets T B) :
    cosetLength hT hB x = 0 ↔ x = Quotient.mk _ 1 := by
  have hs := minimalRepresentative_spec hT hB x
  constructor
  · intro h0
    have h1 : minimalRepresentative hT hB x = 1 := eq_one_of_inversions_eq_zero _ h0
    rw [← Quotient.out_eq x]
    apply Quotient.sound
    have := hs.1
    rw [h1] at this
    exact this
  · rintro rfl
    have hrel : SameDoubleCoset T B (minimalRepresentative hT hB (Quotient.mk _ 1)) 1 :=
      (EKPlatformBijection.doubleCosetSetoid T B).iseqv.trans
        ((EKPlatformBijection.doubleCosetSetoid T B).iseqv.symm hs.1)
        (Quotient.mk_out (s := EKPlatformBijection.doubleCosetSetoid T B) 1)
    have hle := hs.2 1 hrel
    rw [inversions_one] at hle
    exact Nat.le_zero.mp hle

/-- Exactly one double coset has a minimal representative of length `0`. -/
theorem sum_zero_pow_cosetLength {n r c : ℕ} {T : Fin n → Fin r} {B : Fin n → Fin c}
    (hT : Monotone T) (hB : Monotone B) :
    ∑ x : DoubleCosets T B, (0 : k) ^ cosetLength hT hB x = 1 := by
  classical
  rw [Finset.sum_eq_single (Quotient.mk _ 1)]
  · rw [(cosetLength_eq_zero_iff hT hB _).mpr rfl, pow_zero]
  · intro x _ hx
    exact zero_pow ((cosetLength_eq_zero_iff hT hB x).not.mpr hx)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem w_ne {u v : W} (h : u.toList ≠ v.toList) : u ≠ v := fun e => h (congrArg _ e)

theorem sum_get (β : List ℕ) : (∑ i, β.get i) = β.sum := by
  rw [← List.sum_ofFn, List.ofFn_get]

/-! ## q = 0 -/

/-- EK p.8, `q = 0`: `(h_β, h_α) = 1` if `|β| = |α|` and `0` otherwise (any `k`). -/
theorem form_zero_hWords (β α : List ℕ) :
    form (0 : k) (hWord k β) (hWord k α) = if β.sum = α.sum then 1 else 0 := by
  rw [form_hWords, sourceFormAll]
  by_cases hd : (∑ i, β.get i) = ∑ j, α.get j
  · rw [dif_pos hd, if_pos (by simpa only [sum_get] using hd), sourceForm]
    exact sum_zero_pow_cosetLength _ _
  · rw [dif_neg hd, if_neg (by simpa only [sum_get] using hd)]

theorem hWord_partWord (w : W) : ∃ β : List ℕ, wordBasis k w = hWord k β ∧ β.sum = degree w :=
  ⟨List.ofFn (parts w), by rw [← vWord, vWord_parts], by
    rw [List.sum_ofFn, parts_sum]⟩

theorem form_zero_basis (v w : W) :
    form (0 : k) (wordBasis k v) (wordBasis k w) = if degree v = degree w then 1 else 0 := by
  obtain ⟨β, hv, hβ⟩ := hWord_partWord (k := k) v
  obtain ⟨α, hw, hα⟩ := hWord_partWord (k := k) w
  rw [hv, hw, form_zero_hWords, hβ, hα]

theorem h_eq_wordBasis (n : ℕ) : ∃ w : W, degree w = n ∧ h k n = wordBasis k w := by
  cases n with
  | zero => exact ⟨1, rfl, by simp⟩
  | succ n => exact ⟨FreeMonoid.of n, rfl, (wordBasis_of k n).symm⟩

/-- At `q = 0` every word of degree `n` is congruent to `hₙ` modulo the radical. -/
theorem word_sub_h_mem_radical_zero (w : W) :
    wordBasis k w - h k (degree w) ∈ radical (0 : k) := by
  obtain ⟨u, hu, he⟩ := h_eq_wordBasis (k := k) (degree w)
  rw [he]
  intro y
  induction y using basis_induction k (wordBasis k) with
  | hz => simp
  | ha y z hy hz => simp only [map_add, hy, hz, add_zero]
  | hb v r =>
    simp only [map_smul, map_sub, LinearMap.sub_apply, form_zero_basis, hu, sub_self,
      smul_zero]

variable (k) in
/-- The image in `Λ₀` of the degree-`n` part `Λ'ₙ`. -/
def degreePiece0 (n : ℕ) : Submodule k (Lam (0 : k)) :=
  Submodule.span k (piQ (0 : k) '' {x | ∃ w : W, degree w = n ∧ x = wordBasis k w})

theorem degreePiece0_eq_span (n : ℕ) :
    degreePiece0 k n = Submodule.span k {piQ (0 : k) (h k n)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    have he : piQ (0 : k) (wordBasis k w) = piQ (0 : k) (h k n) := by
      rw [← sub_eq_zero, ← map_sub, piQ_eq_zero_iff, ← hw]
      exact word_sub_h_mem_radical_zero w
    rw [he]
    exact Submodule.subset_span rfl
  · apply Submodule.span_le.mpr
    rintro _ rfl
    obtain ⟨w, hw, he⟩ := h_eq_wordBasis (k := k) n
    exact Submodule.subset_span ⟨_, ⟨w, hw, he⟩, rfl⟩

theorem form_zero_h_self (n : ℕ) : form (0 : k) (h k n) (h k n) = 1 := by
  obtain ⟨w, _, he⟩ := h_eq_wordBasis (k := k) n
  rw [he, form_zero_basis, if_pos rfl]

/-- `hₙ` as an element of the degree-`n` part of `Λ₀`. -/
def hElem0 (n : ℕ) : degreePiece0 k n :=
  ⟨piQ (0 : k) (h k n), by rw [degreePiece0_eq_span]; exact Submodule.subset_span rfl⟩

theorem hElem0_linearIndependent (n : ℕ) :
    LinearIndependent k (fun _ : Fin 1 => hElem0 (k := k) n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [Fin.sum_univ_one] at hg
  have h1 : quotientForm (0 : k) (g 0 • piQ (0 : k) (h k n)) (piQ (0 : k) (h k n)) = 0 := by
    have h2 : g 0 • piQ (0 : k) (h k n) = 0 := congrArg Subtype.val hg
    rw [h2, map_zero, LinearMap.zero_apply]
  rw [map_smul, LinearMap.smul_apply, quotientForm_pi, form_zero_h_self, smul_eq_mul,
    mul_one] at h1
  exact h1

theorem hElem0_span (n : ℕ) :
    ⊤ ≤ Submodule.span k (Set.range (fun _ : Fin 1 => hElem0 (k := k) n)) := by
  rintro ⟨x, hx⟩ -
  rw [degreePiece0_eq_span, Submodule.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  have hr : (⟨r • piQ (0 : k) (h k n), hx⟩ : degreePiece0 k n) = r • hElem0 n := rfl
  rw [hr]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨0, rfl⟩)

/-- EK p.8, `q = 0`: `Λₙ` is free of rank one, with basis `hₙ` (any `k`). -/
def degreeBasis0 (n : ℕ) : Basis (Fin 1) k (degreePiece0 k n) :=
  Basis.mk (hElem0_linearIndependent n) (hElem0_span n)

theorem degreePiece0_finrank [Nontrivial k] (n : ℕ) :
    Module.finrank k (degreePiece0 k n) = 1 := by
  rw [Module.finrank_eq_card_basis (degreeBasis0 n), Fintype.card_fin]

/-- EK p.8, `q = 0`: the form degenerates (`h₁h₁ - h₂` is a nonzero radical element). -/
theorem form_zero_degenerate [Nontrivial k] :
    h k 1 * h k 1 - h k 2 ≠ 0 ∧ h k 1 * h k 1 - h k 2 ∈ radical (0 : k) := by
  have hw : h k 1 * h k 1 = wordBasis k (FreeMonoid.of 0 * FreeMonoid.of 0) := by
    rw [wordBasis_mul, wordBasis_of]
  have h2 : h k 2 = wordBasis k (FreeMonoid.of 1) := (wordBasis_of k 1).symm
  constructor
  · rw [hw, h2, sub_ne_zero]
    intro he
    exact w_ne (by simp) ((wordBasis k).injective he)
  · rw [hw]
    exact word_sub_h_mem_radical_zero _

/-! ## q = 1 -/

/-- EK p.8, `q = 1`: `(h_β, h_α) = |βS_α|`, the number of double cosets. -/
theorem form_one_hWords (β α : List ℕ) (hd : (∑ i, β.get i) = ∑ j, α.get j) :
    form (1 : k) (hWord k β) (hWord k α) =
      Fintype.card (DoubleCosets (endpoint β.get rfl) (endpoint α.get hd.symm)) := by
  rw [form_hWords, sourceFormAll, dif_pos hd, sourceForm]
  simp

/-- The same count, as the number of `ℕ`-matrices with row sums `β`, column sums `α`
(all literal sequences, including the orthogonal case `|β| ≠ |α|`). -/
theorem form_one_hWords_mat (β α : List ℕ) :
    form (1 : k) (hWord k β) (hWord k α) =
      Fintype.card (EKPairingMatrices.Mat β.get α.get) := by
  rw [form_hWords, sourceFormAll_eq_matForm, matForm]
  simp

/-! ## Cocommutativity iff q = 1 -/

theorem comm_tensorBasis (p : W × W) :
    TensorProduct.comm k (L k) (L k) (tensorBasis k p) = tensorBasis k (p.2, p.1) := by
  rcases p with ⟨a, b⟩
  simp [tensorBasis_apply]

theorem comm_tensorMul_one (x y : LL k) :
    TensorProduct.comm k (L k) (L k) (tensorMul (1 : k) x y) =
      tensorMul (1 : k) (TensorProduct.comm k (L k) (L k) x)
        (TensorProduct.comm k (L k) (L k) y) := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [tensorMul_add_left, map_add, hx, hz]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [tensorMul_add_right, map_add, hy, hz]
    | hb s t =>
      simp only [tensorMul_smul_left, tensorMul_smul_right, map_smul, tensorMul_basis,
        one_pow, one_smul, comm_tensorBasis]

theorem comm_coproduct_h (q : k) (n : ℕ) :
    TensorProduct.comm k (L k) (L k) (coproduct q (h k n)) = coproduct q (h k n) := by
  rw [coproduct_h, map_sum]
  simp only [TensorProduct.comm_tmul]
  apply Fintype.sum_equiv Fin.revPerm
  intro i
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  congr 2 <;> omega

/-- EK p.5: at `q = 1`, `Λ'` is cocommutative. -/
theorem cocommutative_one (x : L k) :
    TensorProduct.comm k (L k) (L k) (coproduct (1 : k) x) = coproduct (1 : k) x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb w r =>
    simp only [map_smul]
    congr 1
    induction w using FreeMonoid.recOn with
    | h0 => simpa using comm_coproduct_h (1 : k) 0
    | ih i w ih =>
      rw [wordBasis_mul, wordBasis_of, coproduct_mul, comm_tensorMul_one, ih,
        comm_coproduct_h]

/-- Coefficient of `h₁ ⊗ h₁h₁` in `Δ(h₂h₁)` versus in its flip. -/
theorem coproduct_h2_h1 (q : k) :
    coproduct q (h k 2 * h k 1) =
      tensorBasis k (1, FreeMonoid.of 1 * FreeMonoid.of 0) +
      q ^ 2 • tensorBasis k (FreeMonoid.of 0, FreeMonoid.of 1) +
      tensorBasis k (FreeMonoid.of 0, FreeMonoid.of 0 * FreeMonoid.of 0) +
      q • tensorBasis k (FreeMonoid.of 0 * FreeMonoid.of 0, FreeMonoid.of 0) +
      tensorBasis k (FreeMonoid.of 1, FreeMonoid.of 0) +
      tensorBasis k (FreeMonoid.of 1 * FreeMonoid.of 0, 1) := by
  rw [coproduct_two]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, tensorBasis_apply, wordBasis_mul,
    wordBasis_of, wordBasis_one, Fin.val_zero, Fin.val_succ, Fin.val_one, Fin.succ_zero_eq_one]
  norm_num
  abel

/-- EK p.5: "The q-bialgebra `Λ'` is cocommutative if and only if `q = 1`" (any `k`). -/
theorem cocommutative_iff (q : k) :
    (∀ x : L k, TensorProduct.comm k (L k) (L k) (coproduct q x) = coproduct q x) ↔ q = 1 := by
  constructor
  · intro hc
    have h := congrArg ((tensorBasis k).coord (FreeMonoid.of 0, FreeMonoid.of 0 * FreeMonoid.of 0))
      (hc (h k 2 * h k 1))
    rw [coproduct_h2_h1] at h
    simp only [map_add, map_smul, tensorBasis_apply, TensorProduct.comm_tmul] at h
    simp only [← tensorBasis_apply, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply] at h
    have e1 : (1 : W) ≠ FreeMonoid.of 0 := w_ne (by simp)
    have e2 : FreeMonoid.of 1 * FreeMonoid.of 0 ≠ FreeMonoid.of 0 := w_ne (by simp)
    have e3 : FreeMonoid.of 1 ≠ FreeMonoid.of 0 * FreeMonoid.of 0 := w_ne (by simp)
    have e4 : FreeMonoid.of 0 ≠ FreeMonoid.of 0 * FreeMonoid.of 0 := w_ne (by simp)
    have e5 : FreeMonoid.of (1 : ℕ) ≠ FreeMonoid.of 0 := w_ne (by simp)
    have e6 : (1 : W) ≠ FreeMonoid.of 0 * FreeMonoid.of 0 := w_ne (by simp)
    simp [e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm] at h
    exact h
  · rintro rfl
    exact cocommutative_one

/-! ## q = 1: the commutators lie in the radical; `Λ₁` is commutative -/

theorem tensorForm_comm (a b : L k) (t : LL k) (q : k) :
    tensorForm q (a ⊗ₜ[k] b) (TensorProduct.comm k (L k) (L k) t) =
      tensorForm q (b ⊗ₜ[k] a) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c d => simp [mul_comm]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- EK p.8, `q = 1`: every commutator `xy - yx` lies in the radical `I₁` (any `k`). -/
theorem commutator_mem_radical_one (x y : L k) : x*y - y*x ∈ radical (1 : k) := by
  intro z
  rw [map_sub, LinearMap.sub_apply, ← adjointness, ← adjointness, ← cocommutative_one z,
    tensorForm_comm, cocommutative_one, sub_self]

/-- EK p.8, `q = 1`: `Λ₁ = Λ'/I₁` is commutative. -/
theorem lam_one_mul_comm (a b : Lam (1 : k)) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := piQ_surjective (1 : k) a
  obtain ⟨y, rfl⟩ := piQ_surjective (1 : k) b
  rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, piQ_eq_zero_iff]
  exact commutator_mem_radical_one x y

end OddMath.Frontier.EKGeneralQ
