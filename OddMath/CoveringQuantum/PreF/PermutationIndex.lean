import OddMath.CoveringQuantum.PreF.PermutationForm

/-!
# A diagnostic for the permutation index direction

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1, displayed finite sum.
For rational crossing parameters of the even A₃ specialization `q = 2`, `dᵢ = 2`,
this calculation distinguishes the printed mixed index convention from the existing
free form. The words are `(2,1,3)` and `(1,3,2)` in one-based vertex labels.
The proof concerns these explicit rational parameters; it does not construct a
specialization homomorphism from the generic covering coefficient ring. It does not
refute the intrinsic matching identity (10.5).
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.PreF.PermutationIndex

/-- Rational crossing parameters for the even A₃ specialization at `q = 2`, `dᵢ = 2`.
Colours `0, 1, 2` correspond to the vertices `1, 2, 3`. -/
def crossing : Bichar ℚ (Fin 3) where
  toFun i j := if i = j then 1 / 16 else if i = 1 ∨ j = 1 then 4 else 1
  symm i j := by simp only [eq_comm, or_comm]

def source : Fin 3 → Fin 3 := Equiv.swap 0 1

def target : Fin 3 → Fin 3 := fun r ↦ source (finRotate 3 r)

@[simp] theorem source_word : List.ofFn source = [1, 0, 2] := by decide

@[simp] theorem target_word : List.ofFn target = [0, 2, 1] := by decide

private lemma printed_match (w : Equiv.Perm (Fin 3)) :
    (∀ r, source (w r) = target r) ↔ w = finRotate 3 := by
  constructor
  · intro h
    ext r : 1
    exact (Equiv.swap 0 1).injective (h r)
  · rintro rfl; exact fun _ ↦ rfl

private lemma corrected_match (w : Equiv.Perm (Fin 3)) :
    (∀ r, source r = target (w r)) ↔ w = (finRotate 3).symm := by
  constructor
  · intro h
    ext r : 1
    apply (finRotate 3).injective
    exact ((Equiv.swap 0 1).injective (h r)).symm.trans (by simp)
  · rintro rfl
    simp [target]

/-- The literal printed colour condition with source-indexed inversion factors. -/
theorem printed_value :
    (∏ _r : Fin 3, (-1 / 15 : ℚ)) * (∑ w : Equiv.Perm (Fin 3),
      if ∀ r, source (w r) = target r then inversionWeight crossing source w else 0) =
        -4 / 3375 := by
  simp_rw [printed_match]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hneg : (-1 : Fin 3) = 2 := rfl
  norm_num [inversionWeight, Finset.prod_filter, Fin.prod_univ_succ, crossing, source,
    Equiv.swap_apply_def, finRotate_apply, finRotate_symm_apply, hneg]

/-- The existing free form at the same rational parameters. -/
theorem form_value :
    form crossing (fun _ ↦ (-1 / 15 : ℚ))
      (monomial ℚ (List.ofFn source)) (monomial ℚ (List.ofFn target)) = -16 / 3375 := by
  rw [form_monomial_permutations]
  simp_rw [corrected_match]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hneg : (-1 : Fin 3) = 2 := rfl
  norm_num [inversionWeight, Finset.prod_filter, Fin.prod_univ_succ, crossing, source,
    Equiv.swap_apply_def, finRotate_apply, finRotate_symm_apply, hneg]
  rw [hneg]
  norm_num

/-- The printed index mixture does not evaluate the existing form at this specialization. -/
theorem form_ne_printed :
    form crossing (fun _ ↦ (-1 / 15 : ℚ))
      (monomial ℚ (List.ofFn source)) (monomial ℚ (List.ofFn target)) ≠
      (∏ _r : Fin 3, (-1 / 15 : ℚ)) * (∑ w : Equiv.Perm (Fin 3),
        if ∀ r, source (w r) = target r then inversionWeight crossing source w else 0) := by
  rw [form_value, printed_value]
  norm_num

end OddMath.CoveringQuantum.PreF.PermutationIndex
