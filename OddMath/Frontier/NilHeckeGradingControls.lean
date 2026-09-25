import OddMath.Frontier.NilHeckeGrading

/-! Hand calculations are recorded in the development notes BEFORE production. These
kernel controls were authored AFTER the first production PASS; no reversed chronology.
Consumer: EKL §2.2 Prop2.11, integer grading not super-degree. -/
namespace OddMath.Frontier.NilHeckeGradingControls
open NilHeckeGrading NilHeckeAction NilCoxeterWords
open scoped BigOperators
noncomputable section

/-- Negative degree is genuinely inhabited by a nonzero element. -/
theorem crossing_nonzero (n : ℕ) (i : Fin (n+1)) : crossing n i ≠ 0 := by
  intro h
  have he := NilHeckeBasis.crossing_dot_left i
  simp only [h, zero_mul, mul_zero, sub_zero] at he
  exact zero_ne_one he

theorem negative_degree : crossing 0 0 ∈ degreePiece 0 (-2) ∧ crossing 0 0 ≠ 0 :=
  ⟨crossing_mem 0, crossing_nonzero 0 0⟩

theorem unit_control (n : ℕ) : (1 : Presented n) ∈ degreePiece n 0 := unit_mem

theorem odd_zero (n : ℕ) (r : ℤ) : degreePiece n (2*r+1)=⊥ :=
  degreePiece_odd n _ (by omega)

theorem ONC_odd_zero (n : ℕ) (r : ℤ) : ONC.degreePiece n (2*r+1)=⊥ :=
  ONC.degreePiece_odd n _ (by omega)

theorem rankTwo_mixed_sign : crossing 0 0 * dot 0 0 + dot 0 1 * crossing 0 0 = 1 := by
  exact eq_sub_iff_add_eq.mp (NilHeckeBasis.crossing_dot_left (n:=0) 0)

theorem rankTwo_mixed_degree :
    crossing 0 0 * dot 0 0 + dot 0 1 * crossing 0 0 ∈ degreePiece 0 0 := by
  apply Submodule.add_mem
  · have h := degreePiece_mul (crossing_mem (n:=0) 0) (dot_mem (n:=0) 0)
    norm_num only at h
    exact h
  · have h := degreePiece_mul (dot_mem (n:=0) 1) (crossing_mem (n:=0) 0)
    norm_num only at h
    exact h

theorem rankTwo_square_degree : crossing 0 0 * crossing 0 0 ∈ degreePiece 0 (-4) := by
 have h := degreePiece_mul (crossing_mem (n:=0) 0) (crossing_mem (n:=0) 0)
 norm_num only at h
 exact h
theorem rankTwo_square_zero : crossing 0 0 * crossing 0 0 = 0 := crossing_square 0

theorem wrong_positive_degree_rejected : crossing 0 0 ∉ degreePiece 0 2 := by
  intro h
  have hcoeff : (NilHeckeBasis.basis 0).repr (crossing 0 0) = 0 := by
    -- Use uniqueness of actual homogeneous decompositions, not an assumed grading.
    obtain ⟨f,hf,huniq⟩ := unique_homogeneous_decomposition (crossing 0 0)
    have hsingle (d : ℤ) (hd : crossing 0 0 ∈ degreePiece 0 d) :
        (Finsupp.single d (crossing 0 0) : ℤ →₀ Presented 0)=f := by
      apply huniq
      constructor
      · intro e
        by_cases he : d=e
        · subst e; simpa using hd
        · simp [Finsupp.single_eq_of_ne he]
      · simp
    have he := (hsingle (-2) (crossing_mem 0)).trans (hsingle 2 h).symm
    have hz : crossing 0 0=0 := by
      have hc := congrArg (fun c : ℤ →₀ Presented 0 => c (-2)) he
      simpa using hc
    simp [hz]
  have hz : crossing 0 0=0 := (NilHeckeBasis.basis 0).repr.injective (by simpa using hcoeff)
  exact crossing_nonzero 0 0 hz

/-- A finite rank-two enumeration used only as a sign/rank control. -/
theorem rankTwo_permutations : (Finset.univ : Finset (Perm 0)) = {1, simple 0} := by decide

theorem rankTwo_rank_negative : Module.finrank ℤ (degreePiece 0 (-2))=1 := by
  rw [degree_finrank_binomial, rankTwo_permutations]
  rw [Finset.sum_pair (by decide : (1 : Perm 0) ≠ simple 0)]
  have h0 : length (1 : Perm 0)=0 := by decide
  have h1 : length (simple (n:=0) 0)=1 := by decide
  norm_num [admissible, h0, h1, Int.toNat_ofNat]

theorem rankTwo_rank_zero : Module.finrank ℤ (degreePiece 0 0)=3 := by
  rw [degree_finrank_binomial, rankTwo_permutations]
  rw [Finset.sum_pair (by decide : (1 : Perm 0) ≠ simple 0)]
  have h0 : length (1 : Perm 0)=0 := by decide
  have h1 : length (simple (n:=0) 0)=1 := by decide
  norm_num [admissible, h0, h1, Int.toNat_ofNat]

theorem rankTwo_rank_two : Module.finrank ℤ (degreePiece 0 2)=5 := by
  rw [degree_finrank_binomial, rankTwo_permutations]
  rw [Finset.sum_pair (by decide : (1 : Perm 0) ≠ simple 0)]
  have h0 : length (1 : Perm 0)=0 := by decide
  have h1 : length (simple (n:=0) 0)=1 := by decide
  norm_num [admissible, h0, h1, Int.toNat_ofNat]
  decide

theorem rankTwo_rank_below : Module.finrank ℤ (degreePiece 0 (-4))=0 := by
  rw [degree_finrank_binomial, rankTwo_permutations]
  rw [Finset.sum_pair (by decide : (1 : Perm 0) ≠ simple 0)]
  have h0 : length (1 : Perm 0)=0 := by decide
  have h1 : length (simple (n:=0) 0)=1 := by decide
  norm_num [admissible, h0, h1, Int.toNat_ofNat]

theorem rankTwo_ONC_polynomial :
    (∑ w : Perm 0, (Polynomial.X : Polynomial ℤ)^length w) = 1+Polynomial.X := by
  rw [ONC.inversion_generating_polynomial]
  norm_num [Finset.prod_range_succ, Finset.sum_range_succ]

/-- Arbitrary-parameter product consumer, with the actual submodule subtype. -/
theorem arbitrary_homogeneous_product (n : ℕ) (a b : ℤ)
    (x : degreePiece n a) (y : degreePiece n b) :
    (x : Presented n)*(y : Presented n) ∈ degreePiece n (a+b) :=
  degreePiece_mul x.property y.property

theorem arbitrary_ONC_product (n : ℕ) (a b : ℤ)
    (x : ONC.degreePiece n a) (y : ONC.degreePiece n b) :
    (x : ONC.Q n)*(y : ONC.Q n) ∈ ONC.degreePiece n (a+b) :=
  ONC.degreePiece_mul x.property y.property

theorem arbitrary_LEFT_basis (n : ℕ) (d : ℤ) (i : DegreeIndex n d) :
    (degreeLeftBasis n d i : Presented n)=NilHeckeBasis.dotMonomial i.val.1 * dividedElement i.val.2 :=
  degreeLeftBasis_apply d i

theorem arbitrary_RIGHT_basis (n : ℕ) (d : ℤ) (i : DegreeIndex n d) :
    (degreeRightBasis n d i : Presented n)=dividedElement i.val.2 * NilHeckeBasis.dotMonomial i.val.1 :=
  degreeRightBasis_apply d i

theorem arbitrary_rank_coefficient (n : ℕ) (d : ℤ) :
    Module.finrank ℤ (degreePiece n d)=∑ w : Perm n, Nat.card {A : Fin (n+2) → ℕ //
      2*(∑ j, A j : ℕ)-2*(length w : ℤ)=d} := degree_finrank_coefficient n d

theorem arbitrary_unique_decomposition (n : ℕ) (x : Presented n) :
    ∃! f : ℤ →₀ Presented n, (∀ d, f d ∈ degreePiece n d) ∧ f.sum (fun _ y => y)=x :=
  unique_homogeneous_decomposition x

/-- The separate ONC components, not ranks transported from ONH. -/
theorem rankTwo_ONC_rank_negative : Module.finrank ℤ (ONC.degreePiece 0 (-2))=1 := by
  classical
  rw [ONC.degree_finrank, Nat.card_eq_fintype_card, Fintype.card_subtype, rankTwo_permutations]
  decide

theorem rankTwo_ONC_rank_zero : Module.finrank ℤ (ONC.degreePiece 0 0)=1 := by
  classical
  rw [ONC.degree_finrank, Nat.card_eq_fintype_card, Fintype.card_subtype, rankTwo_permutations]
  decide

theorem rankTwo_ONC_rank_below : Module.finrank ℤ (ONC.degreePiece 0 (-4))=0 := by
  classical
  rw [ONC.degree_finrank, Nat.card_eq_fintype_card, Fintype.card_subtype, rankTwo_permutations]
  decide

end
end OddMath.Frontier.NilHeckeGradingControls
