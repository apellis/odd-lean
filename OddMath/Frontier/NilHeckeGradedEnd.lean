import OddMath.Frontier.NilHeckeEndomorphism
import OddMath.Frontier.NilHeckeGrading

/-! EKL1111.1320v1 pp12–13 (2.52)–(2.54).
Actual integer support grading, right Schubert coefficients, existing equivalences.
Every helper below serves the graded Prop2.13 / Cor2.14 comparison. -/
namespace OddMath.Frontier.NilHeckeGradedEnd
open OddMath.SkewPolynomial (SkewPolynomial monomial generator expSingle)
open NilHeckeAction NilCoxeterWords OddSchubertAction NilHeckeEndomorphism
open scoped BigOperators
noncomputable section

abbrev pdegree {N : ℕ} (a : Fin N → ℕ) : ℤ := 2*((∑ i, a i : ℕ) : ℤ)

def polynomialPiece (N : ℕ) (d : ℤ) : Submodule ℤ (SkewPolynomial N) where
  carrier := {f | ∀ a, pdegree a ≠ d → f a = 0}
  zero_mem' := by intro a _; rfl
  add_mem' hf hg := by intro a ha; simp [hf a ha, hg a ha]
  smul_mem' z f hf := by intro a ha; rw [Finsupp.smul_apply, hf a ha, smul_zero]

def kernelPiece (n : ℕ) (d : ℤ) : Submodule ℤ (K n) where
  carrier := {k | (k : SkewPolynomial (n+2)) ∈ polynomialPiece (n+2) d}
  zero_mem' := (polynomialPiece _ _).zero_mem
  add_mem' := (polynomialPiece _ _).add_mem
  smul_mem' z _ hk := (polynomialPiece _ _).smul_mem z hk

def endDegree {n : ℕ} (d : ℤ) (T : rightKernelEnd n) : Prop :=
  ∀ e (f : SkewPolynomial (n+2)), f ∈ polynomialPiece (n+2) e →
    T.val f ∈ polynomialPiece (n+2) (e+d)

def matrixDegree {n : ℕ} (d : ℤ) (M : Matrix (Perm n) (Perm n) (K n)) : Prop :=
  ∀ i j, M i j ∈ kernelPiece n (d+2*(length j : ℤ)-2*(length i : ℤ))

theorem monomial_mem {N : ℕ} (a : Fin N → ℕ) (z : ℤ) :
    monomial a z ∈ polynomialPiece N (pdegree a) := by
  intro b hb
  exact Finsupp.single_eq_of_ne (fun he => hb (congrArg pdegree he.symm))

theorem polynomial_negative (N : ℕ) (d : ℤ) (hd : d < 0) : polynomialPiece N d = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  ext a
  exact hf a (by dsimp [pdegree]; omega)

theorem polynomial_odd (N : ℕ) (d : ℤ) (hd : d % 2 ≠ 0) : polynomialPiece N d = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  ext a
  exact hf a (by dsimp [pdegree]; omega)

theorem kernel_negative (n : ℕ) (d : ℤ) (hd : d < 0) : kernelPiece n d = ⊥ := by
  apply le_antisymm _ bot_le
  intro k hk
  change k = 0
  apply Subtype.ext
  change (k : SkewPolynomial (n+2)) ∈ polynomialPiece (n+2) d at hk
  rw [polynomial_negative _ _ hd] at hk
  exact hk

theorem kernel_odd (n : ℕ) (d : ℤ) (hd : d % 2 ≠ 0) : kernelPiece n d = ⊥ := by
  apply le_antisymm _ bot_le
  intro k hk
  change k = 0
  apply Subtype.ext
  change (k : SkewPolynomial (n+2)) ∈ polynomialPiece (n+2) d at hk
  rw [polynomial_odd _ _ hd] at hk
  exact hk

theorem support_degree {N : ℕ} {d : ℤ} {f : SkewPolynomial N}
    (hf : f ∈ polynomialPiece N d) {a : Fin N → ℕ} (ha : a ∈ f.support) : pdegree a = d := by
  by_contra h
  exact Finsupp.mem_support_iff.mp ha (hf a h)

theorem pdegree_add {N : ℕ} (a b : Fin N → ℕ) : pdegree (a+b)=pdegree a+pdegree b := by
  simp only [pdegree, Pi.add_apply, Finset.sum_add_distrib, Nat.cast_add]; ring

theorem polynomial_mul {N : ℕ} {d e : ℤ} {f g : SkewPolynomial N}
    (hf : f ∈ polynomialPiece N d) (hg : g ∈ polynomialPiece N e) :
    f*g ∈ polynomialPiece N (d+e) := by
  change f.sum (fun a c => g.sum (fun b z => monomial (a+b) (c*z*OddMath.skewSign a b))) ∈ _
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro b hb
  simpa only [pdegree_add, support_degree hf ha, support_degree hg hb] using
    monomial_mem (a+b) (f a*g b*OddMath.skewSign a b)

theorem one_mem (N : ℕ) : (1 : SkewPolynomial N) ∈ polynomialPiece N 0 := by
  simpa only [pdegree, Pi.zero_apply, Finset.sum_const_zero, Nat.cast_zero, mul_zero] using
    monomial_mem (0 : Fin N → ℕ) 1

theorem generator_mem {N : ℕ} (j : Fin N) : generator j ∈ polynomialPiece N 2 := by
  have h : pdegree (expSingle j)=2 := by simp [pdegree, expSingle]
  simpa only [h] using monomial_mem (expSingle j) 1

/-- Word homogeneity is proved on the actual quotient evaluation. -/
theorem polynomial_word_mem {N : ℕ} (w : List (Fin N)) :
    OddMath.PbwL3.Phi N (PbwRealization.word w) ∈ polynomialPiece N (2*(w.length : ℤ)) := by
  induction w with
  | nil => simpa [PbwRealization.word] using one_mem N
  | cons j w ih =>
    have h := polynomial_mul (generator_mem j) ih
    simpa [PbwRealization.word, OddMath.PbwL3.Phi_q, Nat.cast_add, mul_add, add_comm] using h

theorem divided_word_mem {n : ℕ} (i : Fin (n+1)) (w : List (Fin (n+2))) :
    AllRankDivided.divided i (OddMath.PbwL3.Phi (n+2) (PbwRealization.word w)) ∈
      polynomialPiece (n+2) (2*(w.length : ℤ)-2) := by
  induction w with
  | nil => simp [PbwRealization.word, AllRankDivided.divided_one]
  | cons j w ih =>
    change AllRankDivided.divided i (OddMath.PbwL3.Phi (n+2)
      (OddMath.PbwL2.q (n+2) j * PbwRealization.word w)) ∈ _
    rw [map_mul, OddMath.PbwL3.Phi_q, AllRankDivided.divided_mul,
      AllRankDivided.divided_generator, AllRankDivided.s_generator]
    have ht := polynomial_mul ((polynomialPiece _ _).neg_mem
      (generator_mem (Equiv.swap i.castSucc i.succ j))) ih
    have he : 2*((j::w).length : ℤ)-2 = 2*(w.length : ℤ) := by simp; omega
    rw [he]
    apply Submodule.add_mem
    · split_ifs
      · simpa only [one_mul] using polynomial_word_mem w
      · simp
    · convert ht using 1
      congr 1
      ring

theorem divided_monomial_mem {n : ℕ} (i : Fin (n+1)) (a : Fin (n+2) → ℕ) (z : ℤ) :
    AllRankDivided.divided i (monomial a z) ∈ polynomialPiece (n+2) (pdegree a-2) := by
  have hl : ((PbwRealization.orderedList a).length : ℕ) = ∑ j, a j := by
    rw [← ElementaryBasis.weight_exponents, PbwRealization.exponents_orderedList]
  rw [← PbwRealization.Phi_smul_word, map_zsmul, map_smul]
  simpa only [hl] using (polynomialPiece _ _).smul_mem z (divided_word_mem i (PbwRealization.orderedList a))

theorem divided_mem {n : ℕ} (i : Fin (n+1)) {d : ℤ} {f : SkewPolynomial (n+2)}
    (hf : f ∈ polynomialPiece (n+2) d) :
    AllRankDivided.divided i f ∈ polynomialPiece (n+2) (d-2) := by
  have he := (Finsupp.sum_single f).symm
  rw [he, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  simpa only [support_degree hf ha] using divided_monomial_mem i a (f a)

theorem applyWord_mem {n : ℕ} (w : Word n) {d : ℤ} {f : SkewPolynomial (n+2)}
    (hf : f ∈ polynomialPiece (n+2) d) :
    LongestDivided.applyWord w f ∈ polynomialPiece (n+2) (d-2*(w.length : ℤ)) := by
  induction w with
  | nil => simpa using hf
  | cons i w ih =>
    have h := divided_mem i ih
    convert h using 1
    congr 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem dividedElement_mem {n : ℕ} (w : Perm n) {d : ℤ} {f : SkewPolynomial (n+2)}
    (hf : f ∈ polynomialPiece (n+2) d) :
    dividedElementOperator w f ∈ polynomialPiece (n+2) (d-2*(length w : ℤ)) := by
  rw [dividedElementOperator_eq]
  simpa only [chosenWord_length] using applyWord_mem (chosenWord w) hf

theorem staircase_mem (N : ℕ) : LongestDivided.staircase N ∈ polynomialPiece N (2*(N.choose 2 : ℤ)) := by
  have hs : (∑ i : Fin N, (N-1-i.val))=N.choose 2 := by
    calc
      _ = ∑ i : Fin N, (LongestElementary.longest N i).val := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [LongestElementary.longest_apply, Fin.val_rev]
        omega
      _ = ∑ i : Fin N, i.val := Equiv.sum_comp (LongestElementary.longest N) Fin.val
      _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id, Nat.choose_two_right]
  simpa only [pdegree, hs] using monomial_mem (fun i : Fin N => N-1-i.val) 1

/-- The literal (2.41) polynomial, with the inherited chosen reduced word. -/
theorem schubert_mem {n : ℕ} (w : Perm n) :
    schubert w ∈ polynomialPiece (n+2) (2*(length w : ℤ)) := by
  have h := dividedElement_mem (w⁻¹ * LongestElementary.longest (n+2)) (staircase_mem (n+2))
  have hc := complement_length w
  convert h using 1
  congr 1
  omega

/-- Preservation for the independently defined source-word quotient grading. -/
theorem action_mem {n : ℕ} {d e : ℤ} {a : Presented n}
    (ha : a ∈ NilHeckeGrading.degreePiece n d) {f : SkewPolynomial (n+2)}
    (hf : f ∈ polynomialPiece (n+2) e) : action n a f ∈ polynomialPiece (n+2) (e+d) := by
  rw [NilHeckeGrading.degreePiece_eq_leftPiece] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    rw [NilHeckeBasis.action_basisElement, leftOperator_apply]
    have h := polynomial_mul (monomial_mem i.val.1 1) (dividedElement_mem i.val.2 hf)
    have hi := i.property
    unfold NilHeckeGrading.weight at hi
    convert h using 1
    congr 1
    dsimp [pdegree]
    omega
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add, LinearMap.add_apply] using (polynomialPiece _ _).add_mem hx hy
  | smul z x _ hx => simpa only [map_zsmul, LinearMap.smul_apply] using (polynomialPiece _ _).smul_mem z hx

/-- Homogeneous left multiplication is synthesized in the actual source piece. -/
theorem exists_left_degree {n : ℕ} {d : ℤ} {p : SkewPolynomial (n+2)}
    (hp : p ∈ polynomialPiece (n+2) d) :
    ∃ a : Presented n, a ∈ NilHeckeGrading.degreePiece n d ∧ ∀ f, action n a f = p*f := by
  classical
  refine ⟨∑ A ∈ p.support, p A • NilHeckeBasis.dotMonomial A, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro A hA
    apply Submodule.smul_mem
    simpa only [support_degree hp hA] using NilHeckeGrading.dotMonomial_mem A
  · intro f
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      NilHeckeBasis.action_dotMonomial, ← smul_mul_assoc, ← Finset.sum_mul]
    congr 1
    simpa only [Finsupp.sum, monomial, Finsupp.smul_single, smul_eq_mul, mul_one] using Finsupp.sum_single p

/-- Graded version of integral increasing-length interpolation; no division. -/
theorem interpolate_degree (n : ℕ) (d : ℤ) (y : Perm n → SkewPolynomial (n+2))
    (hy : ∀ w, y w ∈ polynomialPiece (n+2) (2*(length w : ℤ)+d)) :
    ∃ a : Presented n, a ∈ NilHeckeGrading.degreePiece n d ∧ ∀ w, action n a (schubert w) = y w := by
  classical
  have step : ∀ k : ℕ, ∃ a : Presented n, a ∈ NilHeckeGrading.degreePiece n d ∧
      ∀ w, length w < k → action n a (schubert w) = y w := by
    intro k
    induction k with
    | zero => exact ⟨0, Submodule.zero_mem _, by intro w h; omega⟩
    | succ k ih =>
      obtain ⟨a,had,ha⟩ := ih
      have hr (w : Perm n) : y w - action n a (schubert w) ∈
          polynomialPiece (n+2) (2*(length w : ℤ)+d) :=
        (polynomialPiece _ _).sub_mem (hy w) (action_mem had (schubert_mem w))
      choose b hbd hb using fun w => exists_left_degree (hr w)
      let S := Finset.univ.filter (fun w : Perm n => length w = k)
      let c := fun w : Perm n => b w * (SchubertBasis.diagonal w • dividedElement w)
      have hcd (w : Perm n) : c w ∈ NilHeckeGrading.degreePiece n d := by
        have h := NilHeckeGrading.degreePiece_mul (hbd w)
          ((NilHeckeGrading.degreePiece _ _).smul_mem (SchubertBasis.diagonal w)
            (NilHeckeGrading.dividedElement_mem w))
        convert h using 1
        congr 1
        ring
      refine ⟨a + ∑ w ∈ S, c w, (NilHeckeGrading.degreePiece _ _).add_mem had
        (Submodule.sum_mem _ (fun w _ => hcd w)), ?_⟩
      intro v hv
      have hc (w : Perm n) : action n (c w) (schubert v) =
          (y w - action n a (schubert w)) *
            (SchubertBasis.diagonal w • dividedElementOperator w (schubert v)) := by
        simp only [c, action_mul_apply, map_zsmul, LinearMap.smul_apply, hb]
        rfl
      simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply]
      simp_rw [hc]
      by_cases hkv : length v = k
      · rw [Finset.sum_eq_single v]
        · rw [normalized_self, mul_one]; abel
        · intro w hw hne
          have hwk := (Finset.mem_filter.mp hw).2
          rw [action_same_length_distinct w v (hkv.trans hwk.symm) (Ne.symm hne), smul_zero, mul_zero]
        · intro hn
          exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkv⟩)).elim
      · rw [Finset.sum_eq_zero]
        · simpa using ha v (by omega)
        · intro w hw
          have hwk := (Finset.mem_filter.mp hw).2
          rw [action_shorter w v (by omega), smul_zero, mul_zero]
  obtain ⟨a,had,ha⟩ := step ((n+2).choose 2 + 1)
  exact ⟨a,had,fun w => ha w (by have := length_le_max w; omega)⟩

/-- Both directions for the EXISTING action equivalence; no grading by pullback. -/
theorem actionEquiv_degree_iff (n : ℕ) (a : Presented n) (d : ℤ) :
    a ∈ NilHeckeGrading.degreePiece n d ↔ endDegree d (actionEquiv n a) := by
  constructor
  · intro ha e f hf
    exact action_mem ha hf
  · intro h
    obtain ⟨b,hb,hba⟩ := interpolate_degree n d
      (fun w => (actionEquiv n a).val (schubert w)) (fun w => h _ _ (schubert_mem w))
    have he : actionEquiv n b = actionEquiv n a := end_ext _ _ hba
    exact (actionEquiv n).injective he ▸ hb

/-- Inverse RIGHT coordinates are homogeneous. Descending length removes the
longer Schubert terms; the normalized selector has integral diagonal ±1. -/
theorem coordinates_mem {n : ℕ} {d : ℤ} {f : SkewPolynomial (n+2)}
    (hf : f ∈ polynomialPiece (n+2) d) (i : Perm n) :
    coordinates n f i ∈ kernelPiece n (d-2*(length i : ℤ)) := by
  classical
  let c := coordinates n f
  have claim : ∀ k : ℕ, ∀ i : Perm n, (n+2).choose 2 - length i = k →
      (c i : SkewPolynomial (n+2)) ∈ polynomialPiece (n+2) (d-2*(length i : ℤ)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      let term := fun w : Perm n =>
        (SchubertBasis.diagonal i • dividedElementOperator i (schubert w)) *
          (c w : SkewPolynomial (n+2))
      have he : SchubertBasis.diagonal i • dividedElementOperator i f = ∑ w, term w := by
        conv_lhs => rw [← synthesis_coordinates n f]
        simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro w _
        dsimp only [term]
        rw [dividedElementOperator_eq, LongestDivided.applyWord_right_kernel _ _ _ (coordinates n f w).property,
          smul_mul_assoc]
      have hself : term i = (c i : SkewPolynomial (n+2)) := by
        dsimp only [term]
        rw [normalized_self, one_mul]
      have hrest : ∑ w ∈ Finset.univ.erase i, term w ∈ polynomialPiece (n+2) (d-2*(length i : ℤ)) := by
        apply Submodule.sum_mem
        intro w hw
        have hwi := (Finset.mem_erase.mp hw).1
        by_cases hlt : length i < length w
        · have hc := ih ((n+2).choose 2 - length w)
            (by have := length_le_max w; omega) w rfl
          have hs := (polynomialPiece _ _).smul_mem (SchubertBasis.diagonal i)
            (dividedElement_mem i (schubert_mem w))
          have hm := polynomial_mul hs hc
          change term w ∈ _
          convert hm using 1
          congr 1
          ring
        · have hz : dividedElementOperator i (schubert w)=0 := by
            by_cases heq : length w = length i
            · exact action_same_length_distinct i w heq hwi
            · exact action_shorter i w (by omega)
          simp [term, hz]
      have hsum := Finset.sum_erase_add (Finset.univ : Finset (Perm n)) term (Finset.mem_univ i)
      rw [← hsum, hself] at he
      have hc : (c i : SkewPolynomial (n+2)) = SchubertBasis.diagonal i •
          dividedElementOperator i f - ∑ w ∈ Finset.univ.erase i, term w := by rw [he]; abel
      rw [hc]
      exact (polynomialPiece _ _).sub_mem
        ((polynomialPiece _ _).smul_mem _ (dividedElement_mem i hf)) hrest
  exact claim _ i rfl

/-- Exact degreewise characterization for arbitrary actual polynomial vectors. -/
theorem coordinates_degree_iff (n : ℕ) (d : ℤ) (f : SkewPolynomial (n+2)) :
    f ∈ polynomialPiece (n+2) d ↔
      ∀ i, coordinates n f i ∈ kernelPiece n (d-2*(length i : ℤ)) := by
  constructor
  · exact fun hf i => coordinates_mem hf i
  · intro h
    have he := synthesis_coordinates n f
    rw [← he]
    change (∑ i, schubert i * (coordinates n f i : SkewPolynomial (n+2))) ∈ _
    apply Submodule.sum_mem
    intro i _
    have hm := polynomial_mul (schubert_mem i) (h i)
    convert hm using 1
    congr 1
    ring

/-- Existing matrixEquiv preserves AND reflects the column-j shifted grading. -/
theorem matrixEquiv_degree_iff (n : ℕ) (T : rightKernelEnd n) (d : ℤ) :
    endDegree d T ↔ matrixDegree d (matrixEquiv n T) := by
  constructor
  · intro h i j
    have hc := coordinates_mem (h _ _ (schubert_mem j)) i
    change coordinates n (T.val (schubert j)) i ∈ _
    convert hc using 1
    congr 1
    ring
  · intro h e f hf
    rw [polynomial_evaluation n T f]
    apply Submodule.sum_mem
    intro i _
    have hcoeff : ((∑ j, toMatrix n T i j * coordinates n f j : K n) : SkewPolynomial (n+2)) ∈
        polynomialPiece (n+2) (e+d-2*(length i : ℤ)) := by
      simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
      apply Submodule.sum_mem
      intro j _
      have hm := polynomial_mul (h i j) (coordinates_mem hf j)
      convert hm using 1
      congr 1
      ring
    have hm := polynomial_mul (schubert_mem i) hcoeff
    convert hm using 1
    congr 1
    ring

/-- Both inherited equivalences at once, with no surrogates or conclusion assumptions. -/
theorem graded_matrix_corollary (n : ℕ) (a : Presented n) (d : ℤ) :
    a ∈ NilHeckeGrading.degreePiece n d ↔
      matrixDegree d (matrixEquiv n (actionEquiv n a)) :=
  (actionEquiv_degree_iff n a d).trans (matrixEquiv_degree_iff n (actionEquiv n a) d)

/-- The finite graded Schubert-basis rank polynomial in half-physical degree. -/
def schubertRankPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ w : Perm n, Polynomial.X ^ length w

theorem schubert_rank_polynomial (n : ℕ) : schubertRankPolynomial n =
    ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), (Polynomial.X : Polynomial ℤ)^k :=
  NilHeckeGrading.ONC.inversion_generating_polynomial n

/-- Physical degree substitution t=q², not the negative ONC numerator. -/
theorem schubert_physical_rank {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    (∑ w : Perm n, q^(2*length w)) =
      ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), q^(2*k) := by
  simpa only [pow_mul] using NilHeckeGrading.inversion_generating (q^2) (n+2)

/-- Prop2.13's LEFT homogeneous basis, retaining the source multiplication side.
Uniqueness is inherited; homogeneity is supplied here, not assumed. -/
theorem left_homogeneous_basis (n : ℕ) :
    (∀ w : Perm n, schubert w ∈ polynomialPiece (n+2) (2*(length w : ℤ))) ∧
    (∀ f : SkewPolynomial (n+2), ∃! c : Perm n → K n,
      f = ∑ w, (c w : SkewPolynomial (n+2)) * schubert w) :=
  ⟨schubert_mem, SchubertBasis.left_kernel_decomposition_unique n⟩

theorem right_homogeneous_basis (n : ℕ) :
    (∀ w : Perm n, schubert w ∈ polynomialPiece (n+2) (2*(length w : ℤ))) ∧
    (∀ f : SkewPolynomial (n+2), ∃! c : Perm n → K n,
      f = ∑ w, schubert w * (c w : SkewPolynomial (n+2))) :=
  ⟨schubert_mem, SchubertBasis.right_kernel_decomposition_unique n⟩

/-- Literal restrictions, with their maps still the inherited ring equivalences. -/
def actionPieceEquiv (n : ℕ) (d : ℤ) :
    (NilHeckeGrading.degreePiece n d) ≃ {T : rightKernelEnd n // endDegree d T} :=
  (actionEquiv n).toEquiv.subtypeEquiv (fun a => actionEquiv_degree_iff n a d)

def matrixPieceEquiv (n : ℕ) (d : ℤ) :
    {T : rightKernelEnd n // endDegree d T} ≃
      {M : Matrix (Perm n) (Perm n) (K n) // matrixDegree d M} :=
  (matrixEquiv n).toEquiv.subtypeEquiv (fun T => matrixEquiv_degree_iff n T d)

@[simp] theorem actionPieceEquiv_apply (n : ℕ) (d : ℤ) (a : NilHeckeGrading.degreePiece n d) :
    (actionPieceEquiv n d a).val = actionEquiv n a.val := rfl

@[simp] theorem matrixPieceEquiv_apply (n : ℕ) (d : ℤ) (T : {T : rightKernelEnd n // endDegree d T}) :
    (matrixPieceEquiv n d T).val = matrixEquiv n T.val := rfl

end
end OddMath.Frontier.NilHeckeGradedEnd
