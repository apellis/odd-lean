import OddMath.Frontier.OddBialgebraShuffle

/-!
# Young subgroups `S_p × S_q ⊂ S_{p+q}` for arbitrary block sizes

EKL arXiv:1111.1320v1, §6, pp. 46–47. For block sizes `p` and `q = n+2-p` (any `p`, including
windows of size `1`), the blocks are `[0, p)` and `[p, n+2)`.

* `IsYoung p y`: `y` preserves the blocks (the Young subgroup `S_p × S_q`); `IsShuf p u`: `u⁻¹`
  is increasing on each block (the minimal length coset representatives).
* `length_young_mul`: `ℓ(y u) = ℓ(y) + ℓ(u)`; `exists_young_factor`, `young_factor_unique`, and
  `youngFactorEquiv : Young × Shuffle ≃ S_{n+2}`.
-/

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords

variable {n : ℕ} (p : ℕ)

/-- The left block `[0, p)`. -/
def InBlk {k : ℕ} (x : Fin k) : Prop := (x : ℕ) < p

instance {k : ℕ} (x : Fin k) : Decidable (InBlk p x) := inferInstanceAs (Decidable ((x : ℕ) < p))

/-- `y` preserves the two blocks. -/
def IsYoung (y : Perm n) : Prop := ∀ x, InBlk p (y x) ↔ InBlk p x

/-- `u⁻¹` is increasing on each block. -/
def IsShuf (u : Perm n) : Prop :=
  ∀ x z : Fin (n+2), x < z → (InBlk p x ↔ InBlk p z) → u⁻¹ x < u⁻¹ z

instance (y : Perm n) : Decidable (IsYoung p y) := by unfold IsYoung; infer_instance

instance (u : Perm n) : Decidable (IsShuf p u) := by unfold IsShuf; infer_instance

variable {p}

theorem isYoung_one : IsYoung p (1 : Perm n) := fun _ => Iff.rfl

theorem IsYoung.mul {y y' : Perm n} (hy : IsYoung p y) (hy' : IsYoung p y') : IsYoung p (y * y') :=
  fun x => (hy (y' x)).trans (hy' x)

theorem IsYoung.inv {y : Perm n} (hy : IsYoung p y) : IsYoung p y⁻¹ := fun x => by
  rw [← hy, Equiv.Perm.apply_inv_self]

theorem inBlk_lt {x z : Fin (n+2)} (hx : InBlk p x) (hz : ¬ InBlk p z) : x < z := by
  unfold InBlk at hx hz; exact Fin.lt_def.2 (by omega)

theorem IsYoung.lt_iff {y : Perm n} (hy : IsYoung p y) {x z : Fin (n+2)}
    (h : ¬ (InBlk p x ↔ InBlk p z)) : y x < y z ↔ x < z := by
  by_cases hx : InBlk p x
  · have hz : ¬ InBlk p z := fun hz => h (iff_of_true hx hz)
    exact iff_of_true (inBlk_lt ((hy x).2 hx) (fun h' => hz ((hy z).1 h'))) (inBlk_lt hx hz)
  · have hz : InBlk p z := by by_contra hz; exact h (iff_of_false hx hz)
    exact iff_of_false (not_lt.2 (inBlk_lt ((hy z).2 hz) (fun h' => hx ((hy x).1 h'))).le)
      (not_lt.2 (inBlk_lt hz hx).le)

theorem IsShuf.lt_iff {u : Perm n} (hu : IsShuf p u) {i j : Fin (n+2)}
    (h : InBlk p (u i) ↔ InBlk p (u j)) : i < j ↔ u i < u j := by
  constructor
  · intro hij
    rcases lt_trichotomy (u i) (u j) with h' | h' | h'
    · exact h'
    · exact absurd (u.injective h') (ne_of_lt hij)
    · have := hu _ _ h' h.symm
      simp only [Equiv.Perm.inv_apply_self] at this
      exact absurd hij (not_lt.2 this.le)
  · intro h'
    have := hu _ _ h' h
    simpa only [Equiv.Perm.inv_apply_self] using this

/-- `ℓ(y u) = ℓ(y) + ℓ(u)` for `y` in the Young subgroup and `u` a shuffle. -/
theorem length_young_mul {y u : Perm n} (hy : IsYoung p y) (hu : IsShuf p u) :
    length (y * u) = length y + length u := by
  have key : ∀ i j : Fin (n+2),
      (if i < j ∧ y (u j) < y (u i) then 1 else 0) =
        (if u i < u j ∧ y (u j) < y (u i) then 1 else 0) +
          (if i < j ∧ u j < u i then 1 else 0) := by
    intro i j
    by_cases hs : InBlk p (u i) ↔ InBlk p (u j)
    · have h1 := hu.lt_iff hs
      rw [if_neg (show ¬(i < j ∧ u j < u i) from fun h => lt_asymm (h1.1 h.1) h.2), add_zero]
      simp only [h1]
    · have h3 : y (u j) < y (u i) ↔ u j < u i := hy.lt_iff (fun h => hs h.symm)
      rw [if_neg (show ¬(u i < u j ∧ y (u j) < y (u i)) from fun h => lt_asymm h.1 (h3.1 h.2)),
        zero_add]
      simp only [h3]
  change (∑ i, ∑ j, if i < j ∧ y (u j) < y (u i) then 1 else 0) = _
  simp only [key, Finset.sum_add_distrib]
  congr 1
  have e := Equiv.sum_comp u fun a => ∑ b, if a < b ∧ y b < y a then 1 else 0
  show _ = ∑ a, ∑ b, if a < b ∧ y b < y a then 1 else 0
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp u fun b => if u i < b ∧ y b < y (u i) then 1 else 0

theorem isYoung_simple {i : Fin (n+1)} (h : InBlk p i.castSucc ↔ InBlk p i.succ) :
    IsYoung p (simple i) := by
  intro x
  simp only [simple, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · exact Iff.rfl

/-- If `u` is not a shuffle, `u⁻¹` has a descent at two adjacent values of one block. -/
theorem exists_adjacent_descent {w : Perm n} (hw : ¬ IsShuf p w) :
    ∃ i : Fin (n+1), (InBlk p i.castSucc ↔ InBlk p i.succ) ∧ Descent w⁻¹ i := by
  by_contra hc
  push_neg at hc
  apply hw
  have hadj : ∀ i : Fin (n+1), (InBlk p i.castSucc ↔ InBlk p i.succ) →
      w⁻¹ i.castSucc < w⁻¹ i.succ := fun i hi => by
    have := hc i hi
    unfold Descent at this
    exact lt_of_le_of_ne (not_lt.1 this) (values_ne w⁻¹ i)
  have base : ∀ x z : Fin (n+2), (z : ℕ) = x + 1 → (InBlk p x ↔ InBlk p z) →
      w⁻¹ x < w⁻¹ z := by
    intro x z hz hxz
    have hx : (x : ℕ) < n + 1 := by omega
    have h1 : (⟨x, hx⟩ : Fin (n+1)).castSucc = x := Fin.ext rfl
    have h2 : (⟨x, hx⟩ : Fin (n+1)).succ = z := Fin.ext (by simp; omega)
    have := hadj ⟨x, hx⟩ (by rw [h1, h2]; exact hxz)
    rwa [h1, h2] at this
  have key : ∀ d : ℕ, ∀ x z : Fin (n+2), (z : ℕ) = x + d + 1 → (InBlk p x ↔ InBlk p z) →
      w⁻¹ x < w⁻¹ z := by
    intro d
    induction d with
    | zero => intro x z hz hxz; exact base x z (by omega) hxz
    | succ d ih =>
      intro x z hz hxz
      let y : Fin (n+2) := ⟨x + 1, by omega⟩
      have hxy : InBlk p x ↔ InBlk p y := by
        unfold InBlk at hxz ⊢; simp only [y]; constructor <;> intro h <;> omega
      have hyz : InBlk p y ↔ InBlk p z := hxy.symm.trans hxz
      exact (base x y rfl hxy).trans (ih y z (by simp only [y]; omega) hyz)
  intro x z hxz hs
  obtain ⟨d, hd⟩ : ∃ d, (z : ℕ) = x + d + 1 := ⟨z - x - 1, by have := Fin.lt_def.1 hxz; omega⟩
  exact key d x z hd hs

/-- Every `w ∈ S_{n+2}` is `y u` with `y` in the Young subgroup and `u` a shuffle. -/
theorem exists_young_factor (w : Perm n) :
    ∃ y u : Perm n, IsYoung p y ∧ IsShuf p u ∧ w = y * u := by
  induction h : length w using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hw : IsShuf p w
    · exact ⟨1, w, isYoung_one, hw, (one_mul w).symm⟩
    obtain ⟨i, hi, hd⟩ := exists_adjacent_descent hw
    obtain ⟨y, u, hy, hu, hyu⟩ :=
      ih _ (h ▸ length_simple_mul_lt w i hd) (simple i * w) rfl
    refine ⟨simple i * y, u, (isYoung_simple hi).mul hy, hu, ?_⟩
    rw [mul_assoc, ← hyu, ← mul_assoc, simple_mul_simple, one_mul]

/-- The factorization is unique. -/
theorem young_factor_unique {y y' u u' : Perm n} (hy : IsYoung p y) (hy' : IsYoung p y')
    (hu : IsShuf p u) (hu' : IsShuf p u') (h : y * u = y' * u') : y = y' ∧ u = u' := by
  obtain ⟨z, hzdef⟩ : ∃ z, z = y'⁻¹ * y := ⟨_, rfl⟩
  have hz : IsYoung p z := hzdef ▸ hy'.inv.mul hy
  have hzu : z * u = u' := by rw [hzdef, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmono : StrictMono z := by
    intro x x' hxx'
    by_cases hs : InBlk p x ↔ InBlk p x'
    · have hij := hu x x' hxx' hs
      have e1 : z x = u' (u⁻¹ x) := by rw [← hzu, Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self]
      have e2 : z x' = u' (u⁻¹ x') := by
        rw [← hzu, Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self]
      rw [e1, e2]
      refine (hu'.lt_iff ?_).1 hij
      rw [← e1, ← e2, hz, hz]
      exact hs
    · exact (hz.lt_iff hs).2 hxx'
  have hz1 : z = 1 := eq_one_of_strictMono hmono
  have hyy : y = y' := (inv_mul_eq_one.1 (hzdef ▸ hz1)).symm
  refine ⟨hyy, ?_⟩
  rw [← hzu, hz1, one_mul]

/-- The Young subgroup `S_p × S_q`. -/
abbrev YoungT (n p : ℕ) : Type := {y : Perm n // IsYoung p y}

/-- The shuffles. -/
abbrev ShufT (n p : ℕ) : Type := {u : Perm n // IsShuf p u}

theorem isShuf_one : IsShuf p (1 : Perm n) := fun _ _ h _ => by simpa using h

instance : Nonempty (ShufT n p) := ⟨⟨1, isShuf_one⟩⟩

/-- `S_p × S_q × Shuffle ≃ S_{n+2}`, `(y, u) ↦ y u`. -/
noncomputable def youngFactorEquiv : YoungT n p × ShufT n p ≃ Perm n :=
  Equiv.ofBijective (fun x => x.1.1 * x.2.1)
    ⟨fun x x' h => by
      obtain ⟨e1, e2⟩ := young_factor_unique x.1.2 x'.1.2 x.2.2 x'.2.2 h
      exact Prod.ext (Subtype.ext e1) (Subtype.ext e2),
     fun w => by
      obtain ⟨y, u, hy, hu, rfl⟩ := exists_young_factor (p := p) w
      exact ⟨(⟨y, hy⟩, ⟨u, hu⟩), rfl⟩⟩

theorem youngFactorEquiv_apply (x : YoungT n p × ShufT n p) :
    youngFactorEquiv x = x.1.1 * x.2.1 := rfl

end OddMath.Frontier.OddBialgebra
