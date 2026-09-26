import OddMath.Frontier.OnhStructure2

/-!
# Minimal coset representatives of `S_a × S_b ⊂ S_{a+b}`

EKL arXiv:1111.1320v1, §6, pp. 46–47: restriction along `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`. The
combinatorial input: every `w ∈ S_{a+b}` factors uniquely as `w = (y₁ × y₂) u` with
`y₁ × y₂ = blockPerm y₁ y₂ ∈ S_a × S_b` and `u` a shuffle (`u⁻¹` increasing on `[0, a)` and on
`[a, a+b)`, i.e. `u` a minimal length representative of `(S_a × S_b) u`), and
`ℓ(w) = ℓ(y₁) + ℓ(y₂) + ℓ(u)`.

Here `a = m+2`, `b = m'+2`, `S_{a+b} = Perm (m+2+m')`.

* `IsShuffle`, `Shuffle m m'`; `length_blockPerm_mul` (length additivity);
  `exists_factor` (by descending induction on `ℓ`, peeling off simple reflections inside the
  blocks), `factor_unique`; `factorEquiv : (S_a × S_b) × Shuffle ≃ S_{a+b}`.
* `card_shuffle`: there are `C(a+b, a)` shuffles.
-/

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords OnhStructure OnhWindow

variable {m m' : ℕ}

/-! ### Blocks -/

/-- The left block `[0, m+2)`. -/
def IsLeft (m : ℕ) {k : ℕ} (x : Fin k) : Prop := x.val < m + 2

instance (m : ℕ) {k : ℕ} (x : Fin k) : Decidable (IsLeft m x) :=
  inferInstanceAs (Decidable (x.val < m + 2))

theorem cases_block (x : Fin (m+2+m'+2)) :
    (∃ k : Fin (m+2), x = Fin.castAdd (m'+2) k) ∨ ∃ k : Fin (m'+2), x = Fin.natAdd (m+2) k := by
  by_cases h : x.val < m + 2
  · exact Or.inl ⟨⟨x.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨x.val - (m+2), by omega⟩, Fin.ext (by simp; omega)⟩

theorem isLeft_castAdd (k : Fin (m+2)) :
    IsLeft m (Fin.castAdd (m'+2) k : Fin (m+2+m'+2)) := k.isLt

theorem not_isLeft_natAdd (k : Fin (m'+2)) :
    ¬ IsLeft m (Fin.natAdd (m+2) k : Fin (m+2+m'+2)) := by
  simp [IsLeft]

theorem lt_of_isLeft {x y : Fin (m+2+m'+2)} (hx : IsLeft m x) (hy : ¬ IsLeft m y) : x < y := by
  unfold IsLeft at hx hy
  exact Fin.lt_def.2 (by omega)

theorem isLeft_blockPerm (w : Perm m) (v : Perm m') (x : Fin (m+2+m'+2)) :
    IsLeft m (blockPerm w v x) ↔ IsLeft m x := by
  rcases cases_block x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [blockPerm_castAdd]
    exact iff_of_true (isLeft_castAdd _) (isLeft_castAdd _)
  · rw [blockPerm_natAdd]
    exact iff_of_false (not_isLeft_natAdd _) (not_isLeft_natAdd _)

/-- `y₁ × y₂` preserves the order between the two blocks. -/
theorem blockPerm_lt_iff (w : Perm m) (v : Perm m') {x y : Fin (m+2+m'+2)}
    (h : ¬ (IsLeft m x ↔ IsLeft m y)) : blockPerm w v x < blockPerm w v y ↔ x < y := by
  by_cases hx : IsLeft m x
  · have hy : ¬ IsLeft m y := fun hy => h (iff_of_true hx hy)
    exact iff_of_true (lt_of_isLeft ((isLeft_blockPerm w v x).2 hx)
      (fun h' => hy ((isLeft_blockPerm w v y).1 h'))) (lt_of_isLeft hx hy)
  · have hy : IsLeft m y := by by_contra hy; exact h (iff_of_false hx hy)
    exact iff_of_false (not_lt.2 (lt_of_isLeft ((isLeft_blockPerm w v y).2 hy)
      (fun h' => hx ((isLeft_blockPerm w v x).1 h'))).le) (not_lt.2 (lt_of_isLeft hy hx).le)

theorem blockPerm_inv (w : Perm m) (v : Perm m') : (blockPerm w v)⁻¹ = blockPerm w⁻¹ v⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← blockPerm_mul, mul_inv_cancel, mul_inv_cancel, blockPerm_one]

/-! ### Shuffles -/

/-- `u` is a shuffle: `u⁻¹` is increasing on each block. -/
def IsShuffle (u : Perm (m+2+m')) : Prop :=
  StrictMono (fun k : Fin (m+2) => u⁻¹ (Fin.castAdd (m'+2) k)) ∧
    StrictMono (fun k : Fin (m'+2) => u⁻¹ (Fin.natAdd (m+2) k))

instance (u : Perm (m+2+m')) : Decidable (IsShuffle u) := by
  unfold IsShuffle StrictMono
  infer_instance

/-- Positions in the same block are ordered as their values. -/
theorem IsShuffle.lt_iff {u : Perm (m+2+m')} (hu : IsShuffle u) {i j : Fin (m+2+m'+2)}
    (h : IsLeft m (u i) ↔ IsLeft m (u j)) : i < j ↔ u i < u j := by
  rcases cases_block (u i) with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    rcases cases_block (u j) with ⟨k', hk'⟩ | ⟨k', hk'⟩
  · have hi : i = u⁻¹ (Fin.castAdd (m'+2) k) := by rw [← hk, Equiv.Perm.inv_apply_self]
    have hj : j = u⁻¹ (Fin.castAdd (m'+2) k') := by rw [← hk', Equiv.Perm.inv_apply_self]
    rw [hk, hk', hi, hj]
    refine (hu.1.lt_iff_lt (a := k) (b := k')).trans ?_
    simp only [Fin.lt_def, Fin.coe_castAdd]
  · exact absurd (h.1 (hk ▸ isLeft_castAdd k)) (hk' ▸ not_isLeft_natAdd k')
  · exact absurd (h.2 (hk' ▸ isLeft_castAdd k')) (hk ▸ not_isLeft_natAdd k)
  · have hi : i = u⁻¹ (Fin.natAdd (m+2) k) := by rw [← hk, Equiv.Perm.inv_apply_self]
    have hj : j = u⁻¹ (Fin.natAdd (m+2) k') := by rw [← hk', Equiv.Perm.inv_apply_self]
    rw [hk, hk', hi, hj]
    refine (hu.2.lt_iff_lt (a := k) (b := k')).trans ?_
    simp only [Fin.lt_def, Fin.coe_natAdd, Nat.add_lt_add_iff_left]

/-- **Length additivity**: `ℓ((y₁ × y₂) u) = ℓ(y₁ × y₂) + ℓ(u)` for a shuffle `u`. -/
theorem length_blockPerm_mul (w : Perm m) (v : Perm m') {u : Perm (m+2+m')}
    (hu : IsShuffle u) : length (blockPerm w v * u) = length (blockPerm w v) + length u := by
  set Y := blockPerm w v
  have key : ∀ i j : Fin (m+2+m'+2),
      (if i < j ∧ Y (u j) < Y (u i) then 1 else 0) =
        (if u i < u j ∧ Y (u j) < Y (u i) then 1 else 0) +
          (if i < j ∧ u j < u i then 1 else 0) := by
    intro i j
    by_cases hs : IsLeft m (u i) ↔ IsLeft m (u j)
    · have h1 := hu.lt_iff hs
      rw [if_neg (show ¬(i < j ∧ u j < u i) from fun h => lt_asymm (h1.1 h.1) h.2), add_zero]
      simp only [h1]
    · have h3 : Y (u j) < Y (u i) ↔ u j < u i := blockPerm_lt_iff w v (fun h => hs h.symm)
      rw [if_neg (show ¬(u i < u j ∧ Y (u j) < Y (u i)) from fun h => lt_asymm h.1 (h3.1 h.2)),
        zero_add]
      simp only [h3]
  change (∑ i, ∑ j, if i < j ∧ Y (u j) < Y (u i) then 1 else 0) = _
  simp only [key, Finset.sum_add_distrib]
  congr 1
  have e := Equiv.sum_comp u fun p => ∑ q, if p < q ∧ Y q < Y p then 1 else 0
  show _ = ∑ p, ∑ q, if p < q ∧ Y q < Y p then 1 else 0
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp u fun q => if u i < q ∧ Y q < Y (u i) then 1 else 0

/-! ### Factorization -/

theorem simple_mul_simple {n : ℕ} (i : Fin (n+1)) : simple i * simple i = 1 :=
  Equiv.swap_mul_self _ _

/-- Peeling off a descent of `w⁻¹` at the simple reflection `s_i`. -/
theorem length_simple_mul_lt {n : ℕ} (w : Perm n) (i : Fin (n+1)) (h : Descent w⁻¹ i) :
    length (simple i * w) < length w := by
  have h1 := length_descend w⁻¹ i h
  have h2 : (simple i * w)⁻¹ = w⁻¹ * simple i := by
    rw [mul_inv_rev, simple, Equiv.swap_inv]
  rw [← OddSchubertAction.length_inv (simple i * w), h2, ← OddSchubertAction.length_inv w]
  omega

theorem descent_of_not_lt {n : ℕ} {w : Perm n} {i : Fin (n+1)}
    (h : ¬ w⁻¹ i.castSucc < w⁻¹ i.succ) : Descent w⁻¹ i := by
  have hne : w⁻¹ i.castSucc ≠ w⁻¹ i.succ := values_ne w⁻¹ i
  exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne)

/-- Every `w ∈ S_{a+b}` is `(y₁ × y₂) u` with `u` a shuffle. -/
theorem exists_factor (w : Perm (m+2+m')) :
    ∃ (y : Perm m × Perm m') (u : Perm (m+2+m')), IsShuffle u ∧ w = blockPerm y.1 y.2 * u := by
  induction h : length w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : IsShuffle w
    · exact ⟨(1, 1), w, hw, by rw [blockPerm_one, one_mul]⟩
    rw [IsShuffle, Fin.strictMono_iff_lt_succ, Fin.strictMono_iff_lt_succ, not_and_or] at hw
    rcases hw with hw | hw
    · push_neg at hw
      obtain ⟨k, hk⟩ := hw
      set i := shiftIndex (window_left_le m m') k
      have hc : i.castSucc = Fin.castAdd (m'+2) k.castSucc := Fin.ext (by simp [i])
      have hs : i.succ = Fin.castAdd (m'+2) k.succ := Fin.ext (by simp [i])
      have hd : Descent w⁻¹ i := descent_of_not_lt (by rw [hc, hs]; exact not_lt.2 hk)
      obtain ⟨y, u, hu, hy⟩ := ih _ (h ▸ length_simple_mul_lt w i hd) (simple i * w) rfl
      refine ⟨(simple k * y.1, y.2), u, hu, ?_⟩
      rw [show blockPerm (simple k * y.1) y.2 = blockPerm (simple k) 1 * blockPerm y.1 y.2 by
        rw [← blockPerm_mul, one_mul], ← simple_shiftL, mul_assoc, ← hy, ← mul_assoc,
        simple_mul_simple, one_mul]
    · push_neg at hw
      obtain ⟨k, hk⟩ := hw
      set i := shiftIndex (window_right_le m m') k
      have hc : i.castSucc = Fin.natAdd (m+2) k.castSucc := Fin.ext (by simp [i]; omega)
      have hs : i.succ = Fin.natAdd (m+2) k.succ := Fin.ext (by simp [i]; omega)
      have hd : Descent w⁻¹ i := descent_of_not_lt (by rw [hc, hs]; exact not_lt.2 hk)
      obtain ⟨y, u, hu, hy⟩ := ih _ (h ▸ length_simple_mul_lt w i hd) (simple i * w) rfl
      refine ⟨(y.1, simple k * y.2), u, hu, ?_⟩
      rw [show blockPerm y.1 (simple k * y.2) = blockPerm 1 (simple k) * blockPerm y.1 y.2 by
        rw [← blockPerm_mul, one_mul], ← simple_shiftR, mul_assoc, ← hy, ← mul_assoc,
        simple_mul_simple, one_mul]

theorem eq_one_of_strictMono {k : ℕ} {σ : Equiv.Perm (Fin k)} (h : StrictMono σ) : σ = 1 := by
  have := (h.range_inj strictMono_id).1 (by rw [σ.surjective.range_eq, Set.range_id])
  exact Equiv.ext fun x => congrFun this x

/-- A block permutation carrying a shuffle to a shuffle is trivial. -/
theorem blockPerm_eq_one_of_shuffle {x₁ : Perm m} {x₂ : Perm m'} {u : Perm (m+2+m')}
    (hu : IsShuffle u) (hxu : IsShuffle (blockPerm x₁ x₂ * u)) : x₁ = 1 ∧ x₂ = 1 := by
  have hinv : (blockPerm x₁ x₂ * u)⁻¹ = u⁻¹ * blockPerm x₁⁻¹ x₂⁻¹ := by
    rw [mul_inv_rev, blockPerm_inv]
  obtain ⟨h1, h2⟩ := hxu
  simp only [hinv, Equiv.Perm.mul_apply, blockPerm_castAdd, blockPerm_natAdd] at h1 h2
  refine ⟨inv_eq_one.1 (eq_one_of_strictMono fun k k' hkk' => ?_),
    inv_eq_one.1 (eq_one_of_strictMono fun k k' hkk' => ?_)⟩
  · exact hu.1.lt_iff_lt.1 (h1 hkk')
  · exact hu.2.lt_iff_lt.1 (h2 hkk')

/-- The factorization `w = (y₁ × y₂) u` is unique. -/
theorem factor_unique {y z : Perm m × Perm m'} {u u' : Perm (m+2+m')} (hu : IsShuffle u)
    (hu' : IsShuffle u') (h : blockPerm y.1 y.2 * u = blockPerm z.1 z.2 * u') : y = z ∧ u = u' := by
  have e : blockPerm (z.1⁻¹ * y.1) (z.2⁻¹ * y.2) * u = u' := by
    rw [blockPerm_mul, ← blockPerm_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨e1, e2⟩ := blockPerm_eq_one_of_shuffle hu (e ▸ hu')
  have hy1 : y.1 = z.1 := (inv_mul_eq_one.1 e1).symm
  have hy2 : y.2 = z.2 := (inv_mul_eq_one.1 e2).symm
  refine ⟨Prod.ext hy1 hy2, ?_⟩
  rw [← e, e1, e2, blockPerm_one, one_mul]

/-- The shuffles: minimal length representatives of `(S_a × S_b) \ S_{a+b}`. -/
abbrev Shuffle (m m' : ℕ) : Type := {u : Perm (m+2+m') // IsShuffle u}

/-- `(S_a × S_b) × Shuffle ≃ S_{a+b}`, `((y₁, y₂), u) ↦ (y₁ × y₂) u`. -/
noncomputable def factorEquiv : (Perm m × Perm m') × Shuffle m m' ≃ Perm (m+2+m') :=
  Equiv.ofBijective (fun p => blockPerm p.1.1 p.1.2 * p.2.1)
    ⟨fun p q h => by
      obtain ⟨e1, e2⟩ := factor_unique p.2.2 q.2.2 h
      exact Prod.ext e1 (Subtype.ext e2),
     fun w => by
      obtain ⟨y, u, hu, rfl⟩ := exists_factor w
      exact ⟨(y, ⟨u, hu⟩), rfl⟩⟩

theorem factorEquiv_apply (y : Perm m × Perm m') (u : Shuffle m m') :
    factorEquiv (y, u) = blockPerm y.1 y.2 * u.1 := rfl

/-- There are `C(a+b, a)` shuffles. -/
theorem card_shuffle : Fintype.card (Shuffle m m') = (m+2+m'+2).choose (m+2) := by
  have h := Fintype.card_congr (factorEquiv (m := m) (m' := m'))
  simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] at h
  have hc := Nat.choose_mul_factorial_mul_factorial (show m+2 ≤ m+2+m'+2 by omega)
  rw [show m+2+m'+2 - (m+2) = m'+2 by omega] at hc
  have hpos : 0 < (m+2).factorial * (m'+2).factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Fintype.card (Shuffle m m') * ((m+2).factorial * (m'+2).factorial)
      = (m+2).factorial * (m'+2).factorial * Fintype.card (Shuffle m m') := by ring
    _ = _ := h
    _ = _ := hc.symm
    _ = _ := by ring

end OddMath.Frontier.OddBialgebra
