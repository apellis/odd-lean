import OddMath.SKM.DividedPowerIdempotents
import OddMath.Frontier.Categorification
import OddMath.Frontier.EQOnhDGCompare

/-!
# The odd nilHecke left-module decomposition

The algebraic splitting underlying BE2, arXiv:1701.04133v2, Lemma 11.1.
EKL's (6.1) is transported through the reflected anti-automorphism comparing
their projector with the corrected BE2 longest product. Because this map is
anti-multiplicative, the two splitting maps must be interchanged. This module
uses the existing principal LEFT ideals and splitting equivalence.
-/

namespace OddMath.SKM.DividedPowerDecomposition

open OddMath.Frontier NilHeckeAction BoxPartitionCount Categorification
open DividedPowerIdempotents
open scoped BigOperators

noncomputable section

private def reflection (n : ℕ) : Presented n ≃+ Presented n :=
  (OnhReflection.sigma n).toAddEquiv.trans (NilHeckeRightBasis.reverseEquiv n).toAddEquiv

private theorem reflection_apply (n : ℕ) (x : Presented n) :
    reflection n x = reflectedOpposite n x := rfl

/-- The corrected longest projector is primitive, by the existing integral
corner theorem and the explicit reflected anti-equivalence. -/
theorem oppositeProjector_primitive {n : ℕ} (y : Presented n)
    (h : (oppositeProjector n * y * oppositeProjector n) *
      (oppositeProjector n * y * oppositeProjector n) =
      oppositeProjector n * y * oppositeProjector n) :
    oppositeProjector n * y * oppositeProjector n = 0 ∨
      oppositeProjector n * y * oppositeProjector n = oppositeProjector n := by
  obtain ⟨x, rfl⟩ := (reflection n).surjective y
  have hx : (ZeroHecke.projector n * x * ZeroHecke.projector n) *
      (ZeroHecke.projector n * x * ZeroHecke.projector n) =
      ZeroHecke.projector n * x * ZeroHecke.projector n := by
    apply (reflection n).injective
    simpa only [reflection_apply, reflectedOpposite_mul, mul_assoc,
      oppositeProjector] using h
  rcases OnhStructure.projector_primitive x hx with hx | hx
  · left
    have hh := congrArg (reflection n) hx
    simpa only [map_zero, reflection_apply, reflectedOpposite_mul, mul_assoc,
      oppositeProjector] using hh
  · right
    have hh := congrArg (reflection n) hx
    simpa only [reflection_apply, reflectedOpposite_mul, mul_assoc,
      oppositeProjector] using hh

/-- EKL's splitters with their order interchanged by the anti-automorphism. -/
def oddSplitting (n : ℕ) :
    Splitting (1 : Presented n) (oppositeProjector n) (Sq (n + 2)) where
  σ ℓ := reflectedOpposite n (ThickMatrixUnits.lam ℓ.1)
  lam ℓ := reflectedOpposite n (ThickMatrixUnits.sigma ℓ.1)
  sum_eq := by
    have h := congrArg (reflection n) (sum_eq_61 (n := n))
    simpa only [map_sum, reflection_apply, reflectedOpposite_mul,
      reflectedOpposite_one] using h
  orth i j := by
    by_cases h : i = j
    · subst j
      rw [← reflectedOpposite_mul, orth_61, ite_eq_left rfl, ite_eq_left rfl]
      rfl
    · rw [← reflectedOpposite_mul, orth_61, ite_eq_right (Ne.symm h), ite_eq_right h]
      simp [reflectedOpposite]
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

/-- Decomposition of the identity into orthogonal idempotents in the corrected
BE2 convention. -/
def summand (n : ℕ) (ℓ : Sq (n + 2)) : Presented n :=
  (oddSplitting n).σ ℓ * (oddSplitting n).lam ℓ

theorem sum_summand (n : ℕ) : ∑ ℓ, summand n ℓ = 1 :=
  (oddSplitting n).sum_eq

theorem summand_mul (n : ℕ) (i j : Sq (n + 2)) :
    summand n i * summand n j = if i = j then summand n i else 0 := by
  simp only [summand, mul_assoc]
  rw [← mul_assoc ((oddSplitting n).lam i), (oddSplitting n).orth]
  split_ifs with h
  · subst j
    rw [(oddSplitting n).mul_lam]
  · simp

theorem summand_idempotent (n : ℕ) (i : Sq (n + 2)) :
    IsIdempotentElem (summand n i) := by
  change summand n i * summand n i = summand n i
  simpa using summand_mul n i i

/-- The left regular module as a product of `(n + 2)!` principal LEFT ideals.
Degree and parity data are separate from this underlying linear equivalence. -/
def oddDecomposition (n : ℕ) :
    Presented n ≃ₗ[Presented n] (Sq (n + 2) → leftIdeal (oppositeProjector n)) :=
  (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ leftIdeal_one.symm)).trans
    (oddSplitting n).equiv

/-- Push the constructed splitting along a unital ring homomorphism, for
coefficient extension or the same-colour corner of a quiver Hecke algebra. -/
def oddSplittingMap {A : Type*} [Ring A] {n : ℕ} (f : Presented n →+* A) :
    Splitting (1 : A) (f (oppositeProjector n)) (Sq (n + 2)) where
  σ ℓ := f ((oddSplitting n).σ ℓ)
  lam ℓ := f ((oddSplitting n).lam ℓ)
  sum_eq := by
    simpa only [map_sum, map_mul, map_one] using congrArg f (oddSplitting n).sum_eq
  orth i j := by
    simpa only [map_mul, apply_ite, map_zero] using congrArg f ((oddSplitting n).orth i j)
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

/-- The left-module decomposition after coefficient extension or corner transport.
The homomorphism need not be injective. -/
def oddDecompositionMap {A : Type*} [Ring A] {n : ℕ} (f : Presented n →+* A) :
    A ≃ₗ[A] (Sq (n + 2) → leftIdeal (f (oppositeProjector n))) :=
  (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ leftIdeal_one.symm)).trans
    (oddSplittingMap f).equiv

/-- The indexing set has exactly the required ordinary factorial size. -/
theorem summand_count (a : ℕ) : Fintype.card (Sq a) = a.factorial := by
  simpa using card_Sq a

/-- The same left-module decomposition includes the empty products in ranks
zero and one; the ambient rings are the library's existing all-rank rings. -/
def oddDecompositionAll : (a : ℕ) →
    SmallRank.ONH a ≃ₗ[SmallRank.ONH a] (Sq a → leftIdeal (dividedPower a))
  | 0 => SmallRank.eq_6_1_small (by omega)
  | 1 => SmallRank.eq_6_1_small (by omega)
  | n + 2 => oddDecomposition n

open EQOnhDG NilHeckeGrading ProjectorRank GradedTrace

private theorem reflection_dot {n : ℕ} (j : Fin (n + 2)) :
    reflection n (dot n j) = dot n j.rev := by
  simp [reflection_apply, reflectedOpposite]

private theorem reflection_crossing {n : ℕ} (i : Fin (n + 1)) :
    reflection n (crossing n i) = crossing n i.rev := by
  simp [reflection_apply, reflectedOpposite]

private theorem reflection_word_degree {n : ℕ} (w : List (Letter n)) :
    reflection n (wordValue w) ∈ grading n (halfWordDegree w) := by
  induction w with
  | nil => simpa [wordValue, halfWordDegree, reflection_apply] using one_mem_grading n
  | cons g w ih =>
    simp only [wordValue, halfWordDegree, List.map_cons, List.prod_cons,
      List.sum_cons, reflection_apply, reflectedOpposite_mul] at ih ⊢
    rw [add_comm]
    apply mul_mem_grading ih
    cases g with
    | inl j =>
      change reflection n (dot n j) ∈ grading n 1
      rw [reflection_dot]
      exact dot_mem_grading n j.rev
    | inr i =>
      change reflection n (crossing n i) ∈ grading n (-1)
      rw [reflection_crossing]
      exact crossing_mem_grading n i.rev

/-- Reflection and ordinary opposite multiplication preserve the source grading. -/
theorem reflectedOpposite_degree {n : ℕ} {d : ℤ} {x : Presented n}
    (hx : x ∈ grading n d) : reflectedOpposite n x ∈ grading n d := by
  have hx' : x ∈ degreePiece n (2 * d) := grading_le_degreePiece d hx
  clear hx
  change reflection n x ∈ grading n d
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw : wordDegree w = 2 * d := hw
    rw [wordDegree_eq_two_mul] at hw
    have h : halfWordDegree w = d := by omega
    exact h ▸ reflection_word_degree w
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy => rw [map_zsmul]; exact AddSubgroup.zsmul_mem _ hy r

/-- The existing faithful polynomial action detects the intrinsic degree. -/
private theorem grading_of_action_degree {n : ℕ} {d : ℤ} {x : Presented n}
    (hx : HasDegree (Vd (n + 2)) d (action n x)) : x ∈ grading n d := by
  apply degreePiece_le_grading d
  apply (NilHeckeGradedEnd.actionEquiv_degree_iff n x (2 * d)).mpr
  intro e f hf
  by_cases he : e % 2 = 0
  · have he' : 2 * (e / 2) = e := by omega
    have h := hx (e / 2) f (by simpa [Vd, he'] using hf)
    change action n x f ∈ NilHeckeGradedEnd.polynomialPiece (n + 2) (e + 2 * d)
    convert h using 1
    unfold Vd
    congr 1
    omega
  · rw [NilHeckeGradedEnd.polynomial_odd _ _ he] at hf
    have hf' : f = 0 := hf
    subst f
    simp

/-- Half the degree of the forward splitting map. The dot has source degree `2dᵢ`. -/
def shift (n : ℕ) (ℓ : Sq (n + 2)) : ℤ := -deg61 ℓ.1

/-- The forward splitters have precisely the degree required by Lemma 11.1. -/
theorem sigma_degree (n : ℕ) (ℓ : Sq (n + 2)) :
    (oddSplitting n).σ ℓ ∈ grading n (shift n ℓ) := by
  apply reflectedOpposite_degree
  apply grading_of_action_degree
  simpa [shift, deg61, ThickMatrixUnits.sigmaDeg_extend] using
    ThickMatrixUnits.hasDegree_lam (mem_Sq' ℓ)

/-- The inverse splitters have the opposite degree. -/
theorem lam_degree (n : ℕ) (ℓ : Sq (n + 2)) :
    (oddSplitting n).lam ℓ ∈ grading n (-shift n ℓ) := by
  apply reflectedOpposite_degree
  apply grading_of_action_degree
  simpa [shift, deg61, ThickMatrixUnits.sigmaDeg_extend] using
    ThickMatrixUnits.hasDegree_sigma (mem_Sq' ℓ)

/-- The displayed orthogonal idempotents have degree zero and therefore even parity. -/
theorem summand_degree (n : ℕ) (ℓ : Sq (n + 2)) : summand n ℓ ∈ grading n 0 := by
  simpa [summand] using mul_mem_grading (sigma_degree n ℓ) (lam_degree n ℓ)

/-- Forward homogeneous components: the degree shift is the degree of the splitter. -/
theorem oddDecomposition_degree {n : ℕ} {x : Presented n} {d : ℤ}
    (hx : x ∈ grading n d) (ℓ : Sq (n + 2)) :
    (oddDecomposition n x ℓ : Presented n) ∈ grading n (d + shift n ℓ) :=
  mul_mem_grading hx (sigma_degree n ℓ)

/-- The inverse has the required homogeneous degree on shifted tuples. -/
theorem oddDecomposition_symm_degree {n : ℕ} {d : ℤ}
    (y : Sq (n + 2) → leftIdeal (oppositeProjector n))
    (hy : ∀ ℓ, (y ℓ : Presented n) ∈ grading n (d + shift n ℓ)) :
    (oddDecomposition n).symm y ∈ grading n d := by
  change (∑ ℓ, (y ℓ : Presented n) * (oddSplitting n).lam ℓ) ∈ grading n d
  apply AddSubgroup.sum_mem
  intro ℓ _
  simpa using mul_mem_grading (hy ℓ) (lam_degree n ℓ)

open OddMath.Diagrams.OddNilHecke in
/-- Independent parity preservation of the splitting, not just degree bookkeeping. -/
theorem oddDecomposition_parity {n : ℕ} {x : Presented n} {p : ZMod 2}
    (hx : x ∈ parity n p) (ℓ : Sq (n + 2)) :
    (oddDecomposition n x ℓ : Presented n) ∈ parity n (p + (shift n ℓ : ZMod 2)) :=
  mul_mem_parity hx (grading_le_parity n _ (sigma_degree n ℓ))

open OddMath.Diagrams.OddNilHecke in
/-- The inverse splitting also preserves parity after the specified shifts. -/
theorem oddDecomposition_symm_parity {n : ℕ} {p : ZMod 2}
    (y : Sq (n + 2) → leftIdeal (oppositeProjector n))
    (hy : ∀ ℓ, (y ℓ : Presented n) ∈ parity n (p + (shift n ℓ : ZMod 2))) :
    (oddDecomposition n).symm y ∈ parity n p := by
  change (∑ ℓ, (y ℓ : Presented n) * (oddSplitting n).lam ℓ) ∈ parity n p
  apply AddSubgroup.sum_mem
  intro ℓ _
  have h := mul_mem_parity (hy ℓ) (grading_le_parity n _ (lam_degree n ℓ))
  rw [Int.cast_neg, add_neg_cancel_right] at h
  exact h

/-- With `P = Q^(-dᵢ choose(a,2)) NH_a D_w₀`, the summand exponent is
`dᵢ (2|ℓ| - choose(a,2))`; there is no extra Π shift on `P`. -/
theorem normalized_degree (n : ℕ) (ℓ : Sq (n + 2)) (di : ℤ) :
    di * ((n + 2).choose 2 : ℤ) - 2 * di * shift n ℓ =
      di * (2 * (∑ j, ℓ.1 j : ℕ) - ((n + 2).choose 2 : ℤ)) := by
  let s : ℤ := ((∑ j : Fin (n + 1), ℓ.1 j : ℕ) : ℤ)
  let c : ℤ := (n + 2).choose 2
  change di * c - 2 * di * (-(s - c)) = di * (2 * s - c)
  ring

end
end OddMath.SKM.DividedPowerDecomposition
