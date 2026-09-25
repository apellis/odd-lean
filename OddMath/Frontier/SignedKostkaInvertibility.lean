import OddMath.Frontier.TableauDominance
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Integral inversion of genuine signed Kostka matrices

The entries are the actual normalized signed tableau counts of Ellis
arXiv:1111.3932v1 §2.1 (2.6). Arbitrary finite distinct families are allowed.
-/
namespace OddMath.Frontier.SignedKostkaInvertibility

open TableauDominance
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def kostkaMatrix (lam : I → YoungDiagram) : Matrix I I ℤ :=
  fun i j => signedKostka (lam i) (lam j)

/-- Prefix differences recover the actual length of each row. -/
theorem shapeContent_row (mu : YoungDiagram) (r : ℕ) :
    shapeContent mu (r + 1) = mu.rowLen r := by
  classical
  rw [← content_canonical, TableauContent.content_apply, YoungDiagram.rowLen_eq_card]
  unfold YoungDiagram.row
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [canonical_entry hp]
  omega

theorem shapePrefix_succ (mu : YoungDiagram) (r : ℕ) :
    shapePrefix mu (r + 1) = shapePrefix mu r + mu.rowLen r := by
  rw [← shapeContent_prefix, ← shapeContent_prefix]
  simp only [contentPrefix, Finset.sum_range_succ, shapeContent_row]

/-- No surrogate order: all row-prefix counts determine the genuine diagram. -/
theorem shapePrefix_injective : Function.Injective shapePrefix := by
  intro mu nu h
  have hr (r : ℕ) : mu.rowLen r = nu.rowLen r := by
    have h0 := congrFun h r
    have h1 := congrFun h (r + 1)
    rw [shapePrefix_succ, shapePrefix_succ] at h1
    omega
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hr]

omit [DecidableEq I] in
/-- A nonzero permutation term cannot contain a strict dominance cycle. -/
theorem perm_eq_one_of_nonzero (lam : I → YoungDiagram) (hlam : Function.Injective lam)
    (s : Equiv.Perm I) (hn : ∀ i, signedKostka (lam (s i)) (lam i) ≠ 0) : s = 1 := by
  have hle (i : I) (k : ℕ) : shapePrefix (lam i) k ≤ shapePrefix (lam (s i)) k := by
    by_contra! h
    exact hn i (signedKostka_zero_of_prefix _ _ ⟨k, h⟩)
  have heq (i : I) (k : ℕ) : shapePrefix (lam i) k = shapePrefix (lam (s i)) k := by
    by_contra h
    have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hle j k)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hle i k) h⟩
    have hs := Equiv.sum_comp s (fun j => shapePrefix (lam j) k)
    omega
  apply Equiv.ext
  intro i
  exact hlam (shapePrefix_injective (funext (fun k => (heq i k).symm)))

/-- The Leibniz expansion has only its identity term; no ordering is assumed. -/
theorem kostkaMatrix_det (lam : I → YoungDiagram) (hlam : Function.Injective lam) :
    Matrix.det (kostkaMatrix lam) = 1 := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm I)]
  · simp [kostkaMatrix]
  · intro s _ hs
    have hp : (∏ i, signedKostka (lam (s i)) (lam i)) = 0 := by
      by_contra hn
      apply hs
      apply perm_eq_one_of_nonzero lam hlam s
      intro i hi
      exact hn (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    simp only [kostkaMatrix, hp, smul_zero]
  · simp

noncomputable def kostkaTransform (lam : I → YoungDiagram) (hlam : Function.Injective lam) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) :=
  Matrix.toLinearEquivRight'OfInv
    (Matrix.nonsing_inv_mul _ (by rw [kostkaMatrix_det lam hlam]; exact isUnit_one))
    (Matrix.mul_nonsing_inv _ (by rw [kostkaMatrix_det lam hlam]; exact isUnit_one))

@[simp] theorem kostkaTransform_apply (lam : I → YoungDiagram) (hlam : Function.Injective lam)
    (c : I → ℤ) (j : I) :
    kostkaTransform lam hlam c j = ∑ i, c i * signedKostka (lam i) (lam j) := by
  rfl

theorem kostka_unique_solution (lam : I → YoungDiagram) (hlam : Function.Injective lam)
    (b : I → ℤ) :
    ∃! c : I → ℤ, ∀ j, ∑ i, c i * signedKostka (lam i) (lam j) = b j := by
  refine ⟨(kostkaTransform lam hlam).symm b, ?_, ?_⟩
  · intro j
    simpa only [kostkaTransform_apply] using
      congrFun ((kostkaTransform lam hlam).apply_symm_apply b) j
  · intro c hc
    apply (kostkaTransform lam hlam).injective
    rw [LinearEquiv.apply_symm_apply]
    exact funext hc

/-- Independence of the parent's literal fixed-content tableau polynomials.
Both the content-dependent tilde sign and shape-dependent canonical sign are
units; neither is silently discarded or absorbed into a redefined polynomial. -/
theorem contentPolynomial_family_independent (lam : I → YoungDiagram)
    (hlam : Function.Injective lam) (n : ℕ)
    (hb : ∀ j p, p ∈ (lam j).cells → p.1 < n) (c : I → ℤ)
    (hz : ∀ j, ∑ i, c i • TableauEvaluation.contentPolynomial n (lam i)
      (shapeContent (lam j)) (shapeContent_bounded n (lam j) (hb j)) = 0) :
    ∀ i, c i = 0 := by
  classical
  let d : I → ℤ := fun i => c i * tableauSign (canonicalTableau (lam i))
  have hd : kostkaTransform lam hlam d = 0 := by
    funext j
    have h := congrArg (fun f : SkewPolynomial.SkewPolynomial n =>
      f (fun a : Fin n => shapeContent (lam j) (a.val + 1))) (hz j)
    simp only [contentPolynomial_eq_signedKostka n _ (lam j) (hb j), Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul, SkewPolynomial.monomial,
      Finsupp.single_eq_same, Finsupp.zero_apply] at h
    have he : (-1 : ℤ) ^ (∑ a : Fin n, a.val * shapeContent (lam j) (a.val + 1)) *
        (∑ i, d i * signedKostka (lam i) (lam j)) = 0 := by
      rw [Finset.mul_sum]
      convert h using 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [d]
      ring
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))
  have hd0 : d = 0 := (kostkaTransform lam hlam).injective (by simpa using hd)
  intro i
  have hi := congrFun hd0 i
  have hi' := congrArg (fun x : ℤ => x * tableauSign (canonicalTableau (lam i))) hi
  simpa [d, mul_assoc] using hi'

end OddMath.Frontier.SignedKostkaInvertibility
