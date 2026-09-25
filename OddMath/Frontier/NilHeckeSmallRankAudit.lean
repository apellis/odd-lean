import OddMath.Frontier.NilHeckeSmallRank

/-! Audit / genuine consumers of the EKL small-rank boundary module.

Source: EKL1111.1320v1 Prop 2.13 and graded Cor 2.14, restricted to the
boundary ranks N = 0 and N = 1 (N >= 2 is existing elsewhere and is NOT
restated or weakened here).

This module consumes the production declarations and adds the N = 1 graded
dimension count (degree pieces are rank 1 in even nonnegative degree and zero
otherwise) together with one must-fail negative control: the dot generator is
not of degree 0. Everything is over `ℤ`; no formal Laurent series is built. -/
namespace OddMath.Frontier.NilHeckeSmallRankAudit

open OddMath.Frontier.NilHeckeSmallRank

/-- N = 1: negative-degree dot pieces vanish. -/
theorem dotPiece_neg_bot {d : ℤ} (hd : d < 0) : dotPiece d = ⊥ := by
  haveI := fiber_neg_empty hd
  rw [dotPiece, Set.range_eq_empty, Submodule.span_empty]

/-- N = 1: odd-degree dot pieces vanish. -/
theorem dotPiece_odd_bot {d : ℤ} (hd : d % 2 ≠ 0) : dotPiece d = ⊥ := by
  haveI := fiber_odd_empty hd
  rw [dotPiece, Set.range_eq_empty, Submodule.span_empty]

/-- N = 1: every even nonnegative dot piece is free of rank exactly one
(graded dimension `t^k` at `t = q^2`, read coefficientwise over `ℤ`). -/
theorem dotPiece_even_finrank (k : ℕ) :
    Module.finrank ℤ (dotPiece (2 * (k : ℤ))) = 1 := by
  letI := fiber_even_unique k
  haveI : Fintype (fiber (2 * (k : ℤ))) := Unique.fintype
  rw [dotPiece, finrank_span_eq_card (fiber_linear_independent _),
    Fintype.card_unique]

/-- N = 1 consumer: the dot generator is homogeneous of degree 2 in the
source grading (via the proved degree equivalence). -/
theorem dot_generator_mem_two :
    OddMath.PbwL2.q 1 0 ∈ dotPiece 2 :=
  (degree_equiv 2 _).mpr (dot_action_generator 0)

/-- N = 1 must-fail control: the dot generator is NOT of degree 0. -/
theorem dot_generator_not_mem_zero :
    OddMath.PbwL2.q 1 0 ∉ dotPiece 0 := by
  intro h
  have h1 := (degree_equiv 0 _).mp h
  rw [OddMath.Frontier.NilHeckeSmallRankControls.single_action_hits_generator]
    at h1
  have hd : OddMath.Frontier.NilHeckeGradedEnd.pdegree
      (OddMath.SkewPolynomial.expSingle (0 : Fin 1)) = 2 := by
    simp [OddMath.Frontier.NilHeckeGradedEnd.pdegree,
      OddMath.SkewPolynomial.expSingle]
  have h2 := h1 (OddMath.SkewPolynomial.expSingle (0 : Fin 1)) (by
    rw [hd]; norm_num)
  simp [OddMath.SkewPolynomial.generator, OddMath.SkewPolynomial.monomial] at h2

/-- N = 0 consumer: endomorphisms are scalar and the module has rank one. -/
theorem zero_boundary_summary :
    Module.finrank ℤ (OddMath.PbwL2.Presented 0) = 1 ∧
      Module.finrank ℤ (Module.End ℤ (OddMath.PbwL2.Presented 0)) = 1 ∧
      (∀ d : ℤ, d ≠ 0 →
        OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 0 d = ⊥) :=
  ⟨finrank_presented_zero, finrank_end_zero,
    fun _ hd => polynomial_piece_zero hd⟩

/-- N = 1 consumer: source / action / shifted-matrix degree equivalence at
rank one, bundled. -/
theorem one_boundary_summary (d : ℤ) (a : OddMath.PbwL2.Presented 1) :
    (a ∈ dotPiece d ↔ OddMath.PbwL3.Phi 1 a ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1 d) ∧
    (a ∈ dotPiece d ↔ ∀ i j, shiftMatrix a i j ∈
      OddMath.Frontier.NilHeckeGradedEnd.polynomialPiece 1
        (d + 2 * ((OddMath.Frontier.NilHeckeGrading.inversions j : ℕ) : ℤ)
          - 2 * ((OddMath.Frontier.NilHeckeGrading.inversions i : ℕ) : ℤ))) :=
  ⟨degree_equiv d a, matrix_entry_degree d a⟩

end OddMath.Frontier.NilHeckeSmallRankAudit
