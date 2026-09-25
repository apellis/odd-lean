import OddMath.Frontier.EKSemiorthogonality
import OddMath.Frontier.EKSelfTranspose

/-! Preproduction controls: literal diagonal-cell enumeration and inherited ell.
These controls were compiled before the production construction. -/
namespace OddMath.Frontier.EKSelfTransposeControls
open EKSemiorthogonality

def shape0 : YoungDiagram := ⊥
def shape1 : YoungDiagram := YoungDiagram.ofRowLens [1] (by decide)
def shape21 : YoungDiagram := YoungDiagram.ofRowLens [2,1] (by decide)
def shape22 : YoungDiagram := YoungDiagram.ofRowLens [2,2] (by decide)

def literalHooks (μ : YoungDiagram) : List ℕ :=
  ((List.range μ.card).filter (fun i => (i,i) ∈ μ)).map
    (fun i => 2 * (μ.rowLen i - i) - 1)

theorem empty_control : literalHooks shape0 = [] ∧ ell shape0 = 0 := by simp only [literalHooks, YoungDiagram.rowLen_eq_card]; decide
theorem one_control : literalHooks shape1 = [1] ∧ ell shape1 = 0 := by simp only [literalHooks, YoungDiagram.rowLen_eq_card]; decide
theorem hook_three_control : literalHooks shape21 = [3] ∧ ell shape21 = 1 := by simp only [literalHooks, YoungDiagram.rowLen_eq_card]; decide
theorem hook_three_one_control : literalHooks shape22 = [3,1] ∧ ell shape22 = 1 := by simp only [literalHooks, YoungDiagram.rowLen_eq_card]; decide

theorem transposes : shape0.transpose = shape0 ∧ shape1.transpose = shape1 ∧
    shape21.transpose = shape21 ∧ shape22.transpose = shape22 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply YoungDiagram.ext <;> decide

theorem signs : (-1 : ℤ)^ell shape0 = 1 ∧ (-1 : ℤ)^ell shape1 = 1 ∧
    (-1 : ℤ)^ell shape21 = -1 ∧ (-1 : ℤ)^ell shape22 = -1 := by decide
-- Postproduction: connect the independently checked fixtures to the general maps.
open EKSelfTranspose
private theorem rank_boundary (μ : YoungDiagram) (d : ℕ)
    (hn : (d,d) ∉ μ) (hp : d = 0 ∨ (d-1,d-1) ∈ μ) : rank μ = d := by
  rw [diagonal_iff] at hn
  rcases hp with h | h
  · omega
  · rw [diagonal_iff] at h
    omega

theorem rank0 : rank shape0 = 0 := rank_boundary _ _ (by decide) (by decide)
theorem rank1 : rank shape1 = 1 := rank_boundary _ _ (by decide) (by decide)
theorem rank21 : rank shape21 = 1 := rank_boundary _ _ (by decide) (by decide)
theorem rank22 : rank shape22 = 2 := rank_boundary _ _ (by decide) (by decide)

theorem production_hooks : hooks shape0 = [] ∧ hooks shape1 = [1] ∧
    hooks shape21 = [3] ∧ hooks shape22 = [3,1] := by
  simp only [hooks, rank0, rank1, rank21, rank22, List.ofFn_succ, List.ofFn_zero]
  simp only [YoungDiagram.rowLen_eq_card]
  decide

theorem inverse_three : ofParts ⟨[3], by decide, by
    intro a ha; simp only [List.mem_singleton] at ha; subst a; decide⟩ = shape21 := by
  have h := ofParts_hooks shape21 transposes.2.2.1
  simpa only [production_hooks.2.2.1] using h

theorem inverse_three_one : ofParts ⟨[3,1], by decide, by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide⟩ = shape22 := by
  have h := ofParts_hooks shape22 transposes.2.2.2
  simpa only [production_hooks.2.2.2] using h

def emptyShape : SelfTranspose 0 := ⟨⟨shape0,by decide⟩,transposes.1⟩
def oneShape : SelfTranspose 1 := ⟨⟨shape1,by decide⟩,transposes.2.1⟩

theorem forward_empty : (diagonalHookEquiv 0 emptyShape).val = [] := production_hooks.1
theorem forward_one : (diagonalHookEquiv 1 oneShape).val = [1] := production_hooks.2.1

theorem arbitrary_sign_consumer (n : ℕ) (p : DistinctOddParts n) :
    (-1 : ℤ)^ell ((diagonalHookEquiv n).symm p).val.val =
      (-1 : ℤ)^(p.val.countP (fun a => a % 4 = 3)) := by
  have h := sign_identity ((diagonalHookEquiv n).symm p).val.val
    ((diagonalHookEquiv n).symm p).property
  have hh : hooks ((diagonalHookEquiv n).symm p).val.val = p.val :=
    congrArg Subtype.val ((diagonalHookEquiv n).apply_symm_apply p)
  rwa [hh] at h

end OddMath.Frontier.EKSelfTransposeControls
