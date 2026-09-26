import OddMath.Frontier.EKGeneralQNondeg

/-!
# The leading coefficient of the Gram determinant in degrees ≤ 5

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, p.40: "It is immediate from the definition of
the bilinear form that this determinant is monic in `q`."

By `EKGeneralQNondeg.gram_det_leadingCoeff` the leading coefficient of the degree-`n` Gram
determinant over `ℤ[q]` is the sign of the reversal `α ↦ α^rev` of compositions of `n`.  Computing
that sign from an explicit enumeration of the compositions:

* `n = 1, 2, 4, 5`: the determinant is monic (`gram_det_monic_small`);
* `n = 3`: the leading coefficient is `-1` (`EKGeneralQNondeg.gram_det_three`).

So the printed claim fails exactly at `n = 3` among `n ≤ 5`.
-/
noncomputable section
open Polynomial
namespace OddMath.Frontier.EKGeneralQ

/-- The sign of the reversal can be computed on any enumeration of the compositions. -/
theorem sign_revPerm_of_enum {n m : ℕ} (e : Fin m ≃ Composition n) (σ : Equiv.Perm (Fin m))
    (h : ∀ i, e (σ i) = (e i).reverse) :
    Equiv.Perm.sign (revPerm n) = Equiv.Perm.sign σ := by
  have hp : revPerm n = e.permCongr σ := by
    ext1 x
    obtain ⟨i, rfl⟩ := e.surjective x
    simp [Equiv.permCongr_apply, h]
  rw [hp, Equiv.Perm.sign_permCongr]

/-- An enumeration of `Composition n` by an explicit duplicate-free list of compositions. -/
def enumComp {n : ℕ} (L : List (List ℕ)) (hpos : ∀ l ∈ L, ∀ a ∈ l, 0 < a)
    (hsum : ∀ l ∈ L, l.sum = n) (i : Fin L.length) : Composition n where
  blocks := L.get i
  blocks_pos := fun ha => hpos _ (List.get_mem _ _) _ ha
  blocks_sum := hsum _ (List.get_mem _ _)

theorem enumComp_bijective {n : ℕ} (L : List (List ℕ)) (hpos : ∀ l ∈ L, ∀ a ∈ l, 0 < a)
    (hsum : ∀ l ∈ L, l.sum = n) (hnd : L.Nodup) (hcard : L.length = 2 ^ (n - 1)) :
    Function.Bijective (enumComp L hpos hsum) := by
  rw [Fintype.bijective_iff_injective_and_card, Fintype.card_fin, composition_card]
  refine ⟨?_, hcard⟩
  intro i j hij
  exact (List.nodup_iff_injective_get.mp hnd) (congrArg Composition.blocks hij)

theorem sign_revPerm_of_list {n : ℕ} (L : List (List ℕ)) (hpos : ∀ l ∈ L, ∀ a ∈ l, 0 < a)
    (hsum : ∀ l ∈ L, l.sum = n) (hnd : L.Nodup) (hcard : L.length = 2 ^ (n - 1))
    (σ : Equiv.Perm (Fin L.length)) (h : ∀ i, L.get (σ i) = (L.get i).reverse) :
    Equiv.Perm.sign (revPerm n) = Equiv.Perm.sign σ :=
  sign_revPerm_of_enum (Equiv.ofBijective _ (enumComp_bijective L hpos hsum hnd hcard)) σ
    (fun i => Composition.ext (h i))

/-- The compositions of `5`. -/
def comps5 : List (List ℕ) :=
  [[1,1,1,1,1], [1,1,1,2], [1,1,2,1], [1,2,1,1], [2,1,1,1], [1,1,3], [1,3,1], [3,1,1],
    [1,2,2], [2,1,2], [2,2,1], [1,4], [4,1], [2,3], [3,2], [5]]

theorem sign_revPerm_one : Equiv.Perm.sign (revPerm 1) = 1 := by
  rw [sign_revPerm_of_list (n := 1) [[1]] (by decide) (by decide) (by decide) (by decide) 1
    (by decide)]
  simp

theorem sign_revPerm_two : Equiv.Perm.sign (revPerm 2) = 1 := by
  rw [sign_revPerm_of_list (n := 2) [[1, 1], [2]] (by decide) (by decide) (by decide) (by decide)
    1 (by decide)]
  simp

theorem sign_revPerm_four : Equiv.Perm.sign (revPerm 4) = 1 := by
  rw [sign_revPerm_of_list (n := 4) [[1,1,1,1], [1,1,2], [1,2,1], [2,1,1], [2,2], [1,3], [3,1], [4]]
    (by decide) (by decide) (by decide) (by decide)
    (Equiv.swap (1 : Fin 8) 3 * Equiv.swap 5 6) (by decide)]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem sign_revPerm_five : Equiv.Perm.sign (revPerm 5) = 1 := by
  rw [sign_revPerm_of_list (n := 5) comps5 (by decide) (by decide) (by decide) (by decide)
    (Equiv.swap (1 : Fin 16) 4 * Equiv.swap 2 3 * Equiv.swap 5 7 * Equiv.swap 8 10 *
      Equiv.swap 11 12 * Equiv.swap 13 14) (by decide)]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

/-- EK §5.2 p.40, "this determinant is monic in `q`": true for `n = 1, 2, 4, 5`; false for
`n = 3` (`gram_det_three`). -/
theorem gram_det_monic_small :
    (gram (X : ℤ[X]) 1).det.Monic ∧ (gram (X : ℤ[X]) 2).det.Monic ∧
    (gram (X : ℤ[X]) 4).det.Monic ∧ (gram (X : ℤ[X]) 5).det.Monic ∧
    ¬ (gram (X : ℤ[X]) 3).det.Monic := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Monic, gram_det_leadingCoeff, sign_revPerm_one]; rfl
  · rw [Monic, gram_det_leadingCoeff, sign_revPerm_two]; rfl
  · rw [Monic, gram_det_leadingCoeff, sign_revPerm_four]; rfl
  · rw [Monic, gram_det_leadingCoeff, sign_revPerm_five]; rfl
  · rw [Monic, gram_det_leadingCoeff, gram_det_three.2]
    decide

end OddMath.Frontier.EKGeneralQ
