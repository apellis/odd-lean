import OddMath.Frontier.EQOnhDGRing
import OddMath.Frontier.NilHeckeGrading

/-!
# Comparison with the `q`-grading of `ONH_{n+2}`

Source: A. P. Ellis, M. Khovanov, A. D. Lauda, arXiv:1111.1320v1, §2.2 (the `q`-grading
`deg x_i = 2`, `deg ∂_i = -2`), and A. P. Ellis, Y. Qi, arXiv:1504.01712v2, §2.2.

The `ℤ`-grading `EQOnhDG.grading n` of `ONH_{n+2}` (pulled back from the diagrammatic degree) is
half the `q`-grading `NilHeckeGrading.degreePiece n` (the span of words in dots and crossings of
`q`-degree `d`): `grading_eq_degreePiece` states `grading n k = degreePiece n (2 k)`.
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open NilHeckeAction NilHeckeGrading
open DirectSum

variable {n : ℕ}

/-- Half the `q`-degree of a letter: `1` for a dot, `-1` for a crossing. -/
def halfLetterDegree : Letter n → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- Half the `q`-degree of a word. -/
def halfWordDegree (w : List (Letter n)) : ℤ := (w.map halfLetterDegree).sum

theorem wordDegree_eq_two_mul (w : List (Letter n)) : wordDegree w = 2 * halfWordDegree w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    simp only [wordDegree, halfWordDegree, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    cases g <;> rfl

theorem wordValue_mem_grading (w : List (Letter n)) :
    wordValue w ∈ grading n (halfWordDegree w) := by
  induction w with
  | nil => exact one_mem_grading n
  | cons g w ih =>
    simp only [wordValue, halfWordDegree, List.map_cons, List.prod_cons] at ih ⊢
    refine mul_mem_grading ?_ ih
    cases g with
    | inl j => exact dot_mem_grading n j
    | inr i => exact crossing_mem_grading n i

theorem mul_mem_span_wordValue {y z : Presented n}
    (hy : y ∈ Submodule.span ℤ (Set.range (wordValue (n := n))))
    (hz : z ∈ Submodule.span ℤ (Set.range (wordValue (n := n)))) :
    y * z ∈ Submodule.span ℤ (Set.range (wordValue (n := n))) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      rw [← wordValue_append]
      exact Submodule.subset_span ⟨u ++ v, rfl⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add z z' _ _ hz hz' => rw [mul_add]; exact Submodule.add_mem _ hz hz'
    | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y y' _ _ hy hy' => rw [add_mul]; exact Submodule.add_mem _ hy hy'
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

/-- Every element of `ONH_{n+2}` is a `ℤ`-linear combination of words in dots and crossings. -/
theorem mem_span_wordValue (p : Presented n) :
    p ∈ Submodule.span ℤ (Set.range (wordValue (n := n))) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective p
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    have h : Ideal.Quotient.mk (relIdeal n) (algebraMap ℤ (Free n) r) = r • wordValue [] := by
      simp [wordValue]
    rw [h]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
  | grade1 g =>
    have h : Ideal.Quotient.mk (relIdeal n) (FreeAlgebra.ι ℤ g) = wordValue [g] := by
      rw [wordValue_eq_image]; simp [freeWord]; rfl
    rw [h]
    exact Submodule.subset_span ⟨[g], rfl⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | mul a b ha hb => rw [map_mul]; exact mul_mem_span_wordValue ha hb

theorem degreePiece_le_grading (k : ℤ) : (degreePiece n (2 * k)).toAddSubgroup ≤ grading n k := by
  intro p hp
  change p ∈ degreePiece n (2 * k) at hp
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw : wordDegree w = 2 * k := hw
    rw [wordDegree_eq_two_mul] at hw
    have : halfWordDegree w = k := by omega
    exact this ▸ wordValue_mem_grading w
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy => exact AddSubgroup.zsmul_mem _ hy r

theorem grading_le_degreePiece (k : ℤ) : grading n k ≤ (degreePiece n (2 * k)).toAddSubgroup := by
  let _inst := decomposition n
  intro p hp
  let φ : Presented n →+ Presented n :=
    (grading n k).subtype.comp
      ((DFinsupp.evalAddMonoidHom k).comp (decomposeAddEquiv (grading n)).toAddMonoidHom)
  have hφ : ∀ q, φ q = (decompose (grading n) q k : Presented n) := fun _ => rfl
  have key : ∀ q : Presented n, φ q ∈ degreePiece n (2 * k) := by
    intro q
    induction mem_span_wordValue q using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [hφ]
      by_cases h : halfWordDegree w = k
      · rw [decompose_of_mem_same _ (h ▸ wordValue_mem_grading w), ← h, ← wordDegree_eq_two_mul]
        exact word_mem w
      · rw [decompose_of_mem_ne _ (wordValue_mem_grading w) h]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_zsmul]; exact Submodule.smul_mem _ r hy
  have := key p
  rwa [hφ, decompose_of_mem_same _ hp] at this

/-- **Comparison with the `q`-grading**: the degree-`k` part of `ONH_{n+2}` for the grading of
`EQOnhDG` is the `q`-degree-`2k` part `NilHeckeGrading.degreePiece n (2k)` (the span of words in
dots and crossings of `q`-degree `2k`). -/
theorem grading_eq_degreePiece (k : ℤ) : grading n k = (degreePiece n (2 * k)).toAddSubgroup :=
  le_antisymm (grading_le_degreePiece k) (degreePiece_le_grading k)

end OddMath.Frontier.EQOnhDG

end
