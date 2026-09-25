import OddMath.Frontier.OddSchubertAction
import OddMath.Frontier.PbwEquivalence

/-! EKL1111.1320v1 (2.39), Proposition 2.11 LEFT PBW basis and faithfulness.
The proof normalizes in the actual presented quotient before using operator independence.
Rank is n+2; products act rightmost first. RIGHT basis and graded ranks are not claimed. -/
namespace OddMath.Frontier.NilHeckeBasis
open NilHeckeAction NilCoxeterWords
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
open scoped BigOperators
noncomputable section
variable {n : ℕ}

private theorem relator_zero (r : Free n) (h : Relator n r) :
    Ideal.Quotient.mk (relIdeal n) r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ (relTwoSided n).asIdeal
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span h

theorem dots_anticommute (i j : Fin (n+2)) (h : i ≠ j) :
    dot n i * dot n j + dot n j * dot n i = 0 := by
  simpa only [map_add, map_mul, dot] using relator_zero _ (Relator.dots i j h)

theorem crossing_dot_left (i : Fin (n+1)) :
    crossing n i * dot n i.castSucc = 1 - dot n i.succ * crossing n i := by
  have h := relator_zero _ (Relator.mixedLeft i)
  simp only [map_sub, map_add, map_mul, map_one, dot, crossing, sub_eq_zero] at h
  exact eq_sub_of_add_eq h

theorem crossing_dot_right (i : Fin (n+1)) :
    crossing n i * dot n i.succ = 1 - dot n i.castSucc * crossing n i := by
  have h := relator_zero _ (Relator.mixedRight i)
  simp only [map_sub, map_add, map_mul, map_one, dot, crossing, sub_eq_zero] at h
  rw [add_comm] at h
  exact eq_sub_of_add_eq h

theorem crossing_dot_other (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
    crossing n i * dot n j = -(dot n j * crossing n i) := by
  have h := relator_zero _ (Relator.spectator i j hl hr)
  simp only [map_add, map_mul, dot, crossing] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Unsorted dot word, with repeated generators retained. -/
def dotWord (v : List (Fin (n+2))) : Presented n := (v.map (dot n)).prod
@[simp] theorem dotWord_nil : dotWord ([] : List (Fin (n+2))) = 1 := rfl
@[simp] theorem dotWord_cons (j : Fin (n+2)) (v : List (Fin (n+2))) :
    dotWord (j::v) = dot n j * dotWord v := rfl

def mixedSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (fun vw : List (Fin (n+2)) × Word n =>
    dotWord vw.1 * product vw.2))

theorem mixed_mem (v : List (Fin (n+2))) (w : Word n) :
    dotWord v * product w ∈ mixedSpan n := Submodule.subset_span ⟨(v,w), rfl⟩

theorem dot_mul_mem (j : Fin (n+2)) {x : Presented n} (hx : x ∈ mixedSpan n) :
    dot n j * x ∈ mixedSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨v,w⟩, rfl⟩ := hx
      simpa only [dotWord_cons, mul_assoc] using mixed_mem (j::v) w
  | zero => simpa only [mul_zero] using (mixedSpan n).zero_mem
  | add x y _ _ hx hy => simpa only [mul_add] using (mixedSpan n).add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using (mixedSpan n).smul_mem r hx

/-- Terminating crossing-through-dots induction using the exact two mixed relators. -/
theorem crossing_mixed_mem (i : Fin (n+1)) (v : List (Fin (n+2))) (w : Word n) :
    crossing n i * (dotWord v * product w) ∈ mixedSpan n := by
  induction v with
  | nil => simpa only [dotWord_nil, one_mul, product] using mixed_mem [] (i::w)
  | cons j v ih =>
      rw [dotWord_cons, mul_assoc (dot n j), ← mul_assoc (crossing n i)]
      by_cases hl : j = i.castSucc
      · subst j
        rw [crossing_dot_left, sub_mul, one_mul, mul_assoc]
        exact (mixedSpan n).sub_mem (mixed_mem v w) (dot_mul_mem _ ih)
      · by_cases hr : j = i.succ
        · subst j
          rw [crossing_dot_right, sub_mul, one_mul, mul_assoc]
          exact (mixedSpan n).sub_mem (mixed_mem v w) (dot_mul_mem _ ih)
        · rw [crossing_dot_other i j hl hr, neg_mul, mul_assoc]
          exact (mixedSpan n).neg_mem (dot_mul_mem _ ih)

theorem crossing_mul_mem (i : Fin (n+1)) {x : Presented n} (hx : x ∈ mixedSpan n) :
    crossing n i * x ∈ mixedSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨v,w⟩, rfl⟩ := hx
      exact crossing_mixed_mem i v w
  | zero => simpa only [mul_zero] using (mixedSpan n).zero_mem
  | add x y _ _ hx hy => simpa only [mul_add] using (mixedSpan n).add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using (mixedSpan n).smul_mem r hx

def quotientMap (n : ℕ) : Free n →+* Presented n := Ideal.Quotient.mk (relIdeal n)

/-- Free-algebra induction, not image spanning: arbitrary quotient left factors. -/
theorem free_mul_mem (a : Free n) (x : Presented n) (hx : x ∈ mixedSpan n) :
    quotientMap n a * x ∈ mixedSpan n := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 r => simpa [zsmul_eq_mul] using (mixedSpan n).smul_mem r hx
  | grade1 g =>
      cases g with
      | inl j => exact dot_mul_mem j hx
      | inr i => exact crossing_mul_mem i hx
  | add a b ha hb =>
      rw [map_add, add_mul]
      exact (mixedSpan n).add_mem (ha x hx) (hb x hx)
  | mul a b ha hb =>
      rw [map_mul, mul_assoc]
      exact ha _ (hb x hx)

theorem mem_mixedSpan (x : Presented n) : x ∈ mixedSpan n := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : (1 : Presented n) ∈ mixedSpan n := by simpa [product] using mixed_mem [] []
  simpa only [mul_one] using free_mul_mem a 1 h1

/-- Literal increasing-index product in (2.38); no commutative Finset product. -/
def dotMonomial (A : Fin (n+2) → ℕ) : Presented n :=
  ((List.finRange (n+2)).map (fun i => dot n i ^ A i)).prod

def basisElement (i : (Fin (n+2) → ℕ) × Perm n) : Presented n :=
  dotMonomial i.1 * dividedElement i.2

/-- Universal map from the actual odd polynomial presentation to the dots. -/
def dotFreeMap (n : ℕ) : FreeAlgebra ℤ (Fin (n+2)) →ₐ[ℤ] Presented n :=
  FreeAlgebra.lift ℤ (dot n)

theorem dotFreeMap_kills (a : FreeAlgebra ℤ (Fin (n+2)))
    (ha : a ∈ PbwL2.relIdeal (n+2)) : dotFreeMap n a = 0 := by
  rw [PbwL2.relIdeal, PbwL2.relTwoSided, TwoSidedIdeal.mem_asIdeal] at ha
  induction ha using TwoSidedIdeal.span_induction with
  | mem x hx =>
      obtain ⟨i,j,h,rfl⟩ := hx
      simpa [dotFreeMap] using dots_anticommute i j h
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

def dotMap (n : ℕ) : PbwL2.Presented (n+2) →+* Presented n :=
  Ideal.Quotient.lift _ (dotFreeMap n).toRingHom dotFreeMap_kills

@[simp] theorem dotMap_q (j : Fin (n+2)) : dotMap n (PbwL2.q (n+2) j) = dot n j := by
  change FreeAlgebra.lift ℤ (dot n) (FreeAlgebra.ι ℤ j) = dot n j
  exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem dotMap_word (v : List (Fin (n+2))) :
    dotMap n (PbwNormalization.word v) = dotWord v := by
  induction v with
  | nil => simp
  | cons j v ih =>
      rw [PbwNormalization.word_cons, map_mul, dotMap_q, ih, dotWord_cons]

@[simp] theorem dotWord_canonical (A : Fin (n+2) → ℕ) :
    dotWord (PbwNormalization.canonicalWord A) = dotMonomial A := by
  unfold dotWord PbwNormalization.canonicalWord dotMonomial
  generalize List.finRange (n+2) = l
  induction l with
  | nil => rfl
  | cons j l ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

@[simp] theorem dotMap_ordered (A : Fin (n+2) → ℕ) :
    dotMap n (PbwNormalization.orderedMonomial A) = dotMonomial A := by
  exact (dotMap_word _).trans (dotWord_canonical A)

theorem dotWord_normalize (v : List (Fin (n+2))) :
    dotWord v = (-1 : ℤ) ^ PbwNormalization.sortCrossings v •
      dotMonomial (fun j => v.count j) := by
  simpa only [map_zsmul, dotMap_word, dotMap_ordered] using
    congrArg (dotMap n) (PbwNormalization.word_normalize v)

/-- The integer span of the literal first family in (2.39). -/
def basisSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (@basisElement n))

theorem mixed_mem_basisSpan (v : List (Fin (n+2))) (w : Word n) :
    dotWord v * product w ∈ basisSpan n := by
  rw [dotWord_normalize, smul_mul_assoc]
  apply (basisSpan n).smul_mem
  by_cases hw : Reduced w
  · rcases reduced_dividedElement w hw with h | h
    · rw [h]
      exact Submodule.subset_span ⟨(_, permutation w), rfl⟩
    · rw [h, mul_neg]
      exact (basisSpan n).neg_mem (Submodule.subset_span ⟨(_, permutation w), rfl⟩)
  · rw [nonreduced_zero w hw, mul_zero]
    exact (basisSpan n).zero_mem

/-- Actual quotient-side spanning, before independence or faithfulness is invoked. -/
theorem mem_basisSpan (x : Presented n) : x ∈ basisSpan n := by
  have hle : mixedSpan n ≤ basisSpan n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨v,w⟩,rfl⟩
    exact mixed_mem_basisSpan v w
  exact hle (mem_mixedSpan x)

theorem basisSpan_eq_top (n : ℕ) : basisSpan n = ⊤ := by
  apply top_unique
  intro x _
  exact mem_basisSpan x

/-- Finite integral expansion for EVERY element of Presented, not only the action image. -/
theorem exists_expansion (x : Presented n) :
    ∃ c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ,
      c.sum (fun i a => a • basisElement i) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (mem_basisSpan x)

theorem action_dotWord (v : List (Fin (n+2))) (f : SkewPolynomial (n+2)) :
    action n (dotWord v) f = PbwL3.Phi (n+2) (PbwNormalization.word v) * f := by
  induction v with
  | nil => simp only [dotWord_nil, map_one, PbwNormalization.word_nil, one_mul]; rfl
  | cons j v ih =>
      rw [dotWord_cons, action_mul_apply, action_dot_apply, ih,
        PbwNormalization.word_cons, map_mul, PbwL3.Phi_q, mul_assoc]

theorem action_dotMonomial (A : Fin (n+2) → ℕ) (f : SkewPolynomial (n+2)) :
    action n (dotMonomial A) f = monomial A 1 * f := by
  rw [← dotWord_canonical, action_dotWord]
  change PbwL3.Phi (n+2) (PbwNormalization.orderedMonomial A) * f = _
  rw [PbwEquivalence.Phi_orderedMonomial]

/-- Exact rightmost-first action compatibility with the inherited LEFT operators. -/
theorem action_basisElement (i : (Fin (n+2) → ℕ) × Perm n) :
    action n (basisElement i) = OddSchubertAction.leftOperator i := by
  apply LinearMap.ext
  intro f
  rw [basisElement, action_mul_apply, action_dotMonomial]
  rfl

/-- Arbitrary finite integral quotient relations are trivial. -/
theorem relation_coefficients (s : Finset ((Fin (n+2) → ℕ) × Perm n))
    (c : ((Fin (n+2) → ℕ) × Perm n) → ℤ)
    (h : ∑ i ∈ s, c i • basisElement i = 0) : ∀ i ∈ s, c i = 0 := by
  apply OddSchubertAction.left_relation_coefficients s c
  intro f
  have he := congrArg (fun a => action n a f) h
  simpa only [map_sum, map_zsmul, action_basisElement, map_zero,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using he

theorem basisElement_linearIndependent (n : ℕ) :
    LinearIndependent ℤ (@basisElement n) := by
  apply linearIndependent_iff'.mpr
  exact relation_coefficients

/-- The actual integral LEFT PBW basis of the presented odd nilHecke ring. -/
def basis (n : ℕ) : Basis ((Fin (n+2) → ℕ) × Perm n) ℤ (Presented n) :=
  Basis.mk (basisElement_linearIndependent n) (by rw [← basisSpan_eq_top n]; exact le_rfl)

@[simp] theorem basis_apply (i : (Fin (n+2) → ℕ) × Perm n) :
    basis n i = basisElement i := Basis.mk_apply _ _ _

theorem expansion_unique (c d : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ)
    (h : c.sum (fun i a => a • basisElement i) = d.sum (fun i a => a • basisElement i)) :
    c = d := by
  exact (basisElement_linearIndependent n).finsuppLinearCombination_injective h

/-- Existence AND uniqueness of finite integral coordinates, without assumptions. -/
theorem existsUnique_expansion (x : Presented n) :
    ∃! c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ,
      c.sum (fun i a => a • basisElement i) = x := by
  obtain ⟨c,hc⟩ := exists_expansion x
  exact ⟨c,hc,fun d hd => expansion_unique d c (hd.trans hc.symm)⟩

/-- Faithfulness follows only after quotient-side spanning has been proved. -/
theorem action_injective (n : ℕ) : Function.Injective (action n) := by
  suffices hz : ∀ x : Presented n, action n x = 0 → x = 0 by
    intro x y h
    apply sub_eq_zero.mp
    exact hz (x-y) (by rw [map_sub, h, sub_self])
  intro x hx
  obtain ⟨c,hc⟩ := exists_expansion x
  have he : ∀ f : SkewPolynomial (n+2),
      c.sum (fun i a => a • (monomial i.1 1 * dividedElementOperator i.2 f)) = 0 := by
    intro f
    have h := congrArg (fun a => action n a f) hc
    dsimp only at h
    rw [hx, LinearMap.zero_apply] at h
    simpa only [Finsupp.sum, map_sum, map_zsmul, action_basisElement,
      LinearMap.sum_apply, LinearMap.smul_apply, OddSchubertAction.leftOperator_apply] using h
  have hz := (OddSchubertAction.left_relation_iff c).mp he
  subst c
  simpa using hc.symm

end
end OddMath.Frontier.NilHeckeBasis
