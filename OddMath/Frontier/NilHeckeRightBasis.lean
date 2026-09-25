import OddMath.Frontier.NilHeckeBasis

/-! EKL1111.1320v1 (2.39), Proposition 2.11 RIGHT family.
Rank is n+2; multiplication acts rightmost first. The reversal is constructed
on the actual quotient by checking all seven source relation families. -/
namespace OddMath.Frontier.NilHeckeRightBasis
open NilHeckeAction NilCoxeterWords
open NilHeckeBasis (dotMonomial dotWord)
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open scoped BigOperators
noncomputable section
variable {n : ℕ}

def rightBasisElement (i : (Fin (n+2) → ℕ) × Perm n) : Presented n :=
  dividedElement i.2 * dotMonomial i.1

/-- Free word reversal, valued in the opposite of the actual quotient. -/
def reverseFree (n : ℕ) : Free n →ₐ[ℤ] (Presented n)ᵐᵒᵖ :=
  FreeAlgebra.lift ℤ (Sum.elim (fun j => MulOpposite.op (dot n j))
    (fun i => MulOpposite.op (crossing n i)))

@[simp] theorem reverseFree_dot (j : Fin (n+2)) :
    reverseFree n (dotFree n j) = MulOpposite.op (dot n j) := by
  simp [reverseFree, dotFree]
@[simp] theorem reverseFree_crossing (i : Fin (n+1)) :
    reverseFree n (crossingFree n i) = MulOpposite.op (crossing n i) := by
  simp [reverseFree, crossingFree]

/-- Reversal swaps the two mixed relations; braid is unsigned, distant is signed. -/
theorem reverseFree_relator (r : Free n) (h : Relator n r) : reverseFree n r = 0 := by
  apply MulOpposite.unop_injective
  cases h with
  | square i => simpa using crossing_square i
  | braid i j h => simpa [mul_assoc] using sub_eq_zero.mpr (crossing_braid i j h)
  | dots i j h => simpa [add_comm] using NilHeckeBasis.dots_anticommute i j h
  | distant i j h =>
      simpa [add_comm] using add_eq_zero_iff_eq_neg.mpr (crossing_distant i j h)
  | mixedRight i =>
      simp [NilHeckeBasis.crossing_dot_left]
  | mixedLeft i =>
      simp [NilHeckeBasis.crossing_dot_right, add_comm]
  | spectator i j hl hr =>
      simp [NilHeckeBasis.crossing_dot_other i j hl hr]

theorem reverseFree_ideal (r : Free n) (h : r ∈ relIdeal n) : reverseFree n r = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at h
  induction h using TwoSidedIdeal.span_induction with
  | mem r hr => exact reverseFree_relator r hr
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | neg a _ ha => rw [map_neg, ha, neg_zero]
  | left_absorb a b _ hb => rw [map_mul, hb, mul_zero]
  | right_absorb a b _ hb => rw [map_mul, hb, zero_mul]

/-- Genuine ring homomorphism into the opposite ring, not an assumed anti-map. -/
def reverseHom (n : ℕ) : Presented n →+* (Presented n)ᵐᵒᵖ :=
  Ideal.Quotient.lift _ (reverseFree n).toRingHom reverseFree_ideal

/-- Additive and integral-linear reversal on the presented ring. -/
def reverseLinear (n : ℕ) : Presented n →ₗ[ℤ] Presented n where
  toFun a := MulOpposite.unop (reverseHom n a)
  map_add' a b := by simp
  map_smul' r a := by simp [Int.cast_comm]

@[simp] theorem reverse_dot (j : Fin (n+2)) : reverseLinear n (dot n j) = dot n j := by
  change MulOpposite.unop (reverseFree n (dotFree n j)) = _
  simp
@[simp] theorem reverse_crossing (i : Fin (n+1)) :
    reverseLinear n (crossing n i) = crossing n i := by
  change MulOpposite.unop (reverseFree n (crossingFree n i)) = _
  simp
@[simp] theorem reverse_one : reverseLinear n 1 = 1 := by simp [reverseLinear]
@[simp] theorem reverse_mul (a b : Presented n) :
    reverseLinear n (a*b) = reverseLinear n b * reverseLinear n a := by
  simp [reverseLinear]

/-- All elements, by induction on a free representative. -/
theorem reverse_involutive (n : ℕ) : Function.Involutive (reverseLinear n) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 r => simp [reverseLinear]
  | grade1 g =>
      cases g with
      | inl j => change reverseLinear n (reverseLinear n (dot n j)) = dot n j; simp
      | inr i => change reverseLinear n (reverseLinear n (crossing n i)) = crossing n i; simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | mul a b ha hb =>
      rw [map_mul, reverse_mul, reverse_mul, ha, hb]

/-- No abstract anti-involution framework: this equivalence is for this quotient alone. -/
def reverseEquiv (n : ℕ) : Presented n ≃ₗ[ℤ] Presented n :=
  { reverseLinear n with
    invFun := reverseLinear n
    left_inv := reverse_involutive n
    right_inv := reverse_involutive n }

@[simp] theorem reverse_product (w : Word n) : reverseLinear n (product w) = product w.reverse := by
  induction w with
  | nil => simp [product]
  | cons i w ih => simp [product, ih, List.reverse_cons, product_append]

@[simp] theorem permutation_reverse (w : Word n) : permutation w.reverse = (permutation w)⁻¹ := by
  induction w with
  | nil => simp [permutation]
  | cons i w ih =>
      simp [List.reverse_cons, permutation, ih, mul_inv_rev, simple, Equiv.swap_inv]

theorem reduced_reverse (w : Word n) (h : Reduced w) : Reduced w.reverse := by
  simpa only [Reduced, List.length_reverse, permutation_reverse, OddSchubertAction.length_inv] using h

/-- Fixed chosen reduced words are respected up to an actual unit sign. -/
theorem reverse_divided_signed (w : Perm n) :
    Signed (reverseLinear n (dividedElement w)) (dividedElement w⁻¹) := by
  simpa only [dividedElement, reverse_product, permutation_reverse, chosenWord_permutation] using
    reduced_dividedElement (chosenWord w).reverse (reduced_reverse _ (chosenWord_reduced w))

@[simp] theorem reverse_dotWord (v : List (Fin (n+2))) :
    reverseLinear n (dotWord v) = dotWord v.reverse := by
  induction v with
  | nil => simp
  | cons j v ih =>
      rw [NilHeckeBasis.dotWord_cons, reverse_mul, reverse_dot, ih]
      simp [dotWord, List.reverse_cons, List.map_append, List.prod_append]

theorem reverse_dotMonomial (A : Fin (n+2) → ℕ) :
    reverseLinear n (dotMonomial A) =
      (-1 : ℤ) ^ PbwNormalization.sortCrossings (PbwNormalization.canonicalWord A).reverse •
        dotMonomial A := by
  rw [← NilHeckeBasis.dotWord_canonical, reverse_dotWord, NilHeckeBasis.dotWord_normalize]
  simp only [List.count_reverse, PbwNormalization.canonicalWord_count]
  rw [NilHeckeBasis.dotWord_canonical]

/-- The literal RIGHT family goes to the literal LEFT family, with inverse index. -/
theorem reverse_right_unit (i : (Fin (n+2) → ℕ) × Perm n) :
    ∃ ε : ℤˣ, reverseLinear n (rightBasisElement i) =
      ε • NilHeckeBasis.basisElement (i.1, i.2⁻¹) := by
  rcases reverse_divided_signed i.2 with hw | hw <;>
    rcases neg_one_pow_eq_or ℤ
      (PbwNormalization.sortCrossings (PbwNormalization.canonicalWord i.1).reverse) with ha | ha
  · exact ⟨1, by simp [rightBasisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      NilHeckeBasis.basisElement]⟩
  · exact ⟨-1, by simp [rightBasisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      NilHeckeBasis.basisElement]⟩
  · exact ⟨-1, by simp [rightBasisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      NilHeckeBasis.basisElement]⟩
  · exact ⟨1, by simp [rightBasisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      NilHeckeBasis.basisElement]⟩

theorem reverse_left_unit (i : (Fin (n+2) → ℕ) × Perm n) :
    ∃ ε : ℤˣ, reverseLinear n (NilHeckeBasis.basisElement i) =
      ε • rightBasisElement (i.1, i.2⁻¹) := by
  rcases reverse_divided_signed i.2 with hw | hw <;>
    rcases neg_one_pow_eq_or ℤ
      (PbwNormalization.sortCrossings (PbwNormalization.canonicalWord i.1).reverse) with ha | ha
  · exact ⟨1, by simp [NilHeckeBasis.basisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      rightBasisElement]⟩
  · exact ⟨-1, by simp [NilHeckeBasis.basisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      rightBasisElement]⟩
  · exact ⟨-1, by simp [NilHeckeBasis.basisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      rightBasisElement]⟩
  · exact ⟨1, by simp [NilHeckeBasis.basisElement, reverse_mul, reverse_dotMonomial, hw, ha,
      rightBasisElement]⟩

/-- Integer span in Presented, not merely in its action image. -/
def rightSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (@rightBasisElement n))

theorem reverse_mem_rightSpan (x : Presented n) : reverseLinear n x ∈ rightSpan n := by
  have hx := NilHeckeBasis.mem_basisSpan x
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      obtain ⟨ε,hε⟩ := reverse_left_unit i
      rw [hε]
      exact (rightSpan n).smul_mem (ε : ℤ) (Submodule.subset_span ⟨_,rfl⟩)
  | zero => simpa only [map_zero] using (rightSpan n).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using (rightSpan n).add_mem ha hb
  | smul r a _ ha => simpa only [map_smul] using (rightSpan n).smul_mem r ha

theorem mem_rightSpan (x : Presented n) : x ∈ rightSpan n := by
  simpa only [reverse_involutive n x] using reverse_mem_rightSpan (reverseLinear n x)

theorem rightSpan_eq_top (n : ℕ) : rightSpan n = ⊤ := by
  apply top_unique
  intro x _
  exact mem_rightSpan x

/-- Every actual presented element has finite integral RIGHT coordinates. -/
theorem exists_expansion (x : Presented n) :
    ∃ c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ,
      c.sum (fun i a => a • rightBasisElement i) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (mem_rightSpan x)

/-- Independence transfers through reversal and unit signs, never through ranks. -/
theorem rightBasisElement_linearIndependent (n : ℕ) :
    LinearIndependent ℤ (@rightBasisElement n) := by
  classical
  choose ε hε using (reverse_right_unit (n := n))
  have hi : Function.Injective (fun i : (Fin (n+2) → ℕ) × Perm n => (i.1, i.2⁻¹)) := by
    intro a b h
    have hA := congrArg Prod.fst h
    have hw := congrArg Prod.snd h
    exact Prod.ext hA (inv_injective hw)
  have h := (NilHeckeBasis.basisElement_linearIndependent n).comp _ hi
  have hu := h.units_smul ε
  apply LinearIndependent.of_comp (reverseLinear n)
  convert hu using 1
  funext i
  exact hε i

/-- The actual integral RIGHT PBW basis (EKL (2.39)). -/
def basis (n : ℕ) : Basis ((Fin (n+2) → ℕ) × Perm n) ℤ (Presented n) :=
  Basis.mk (rightBasisElement_linearIndependent n) (by rw [← rightSpan_eq_top n]; exact le_rfl)

@[simp] theorem basis_apply (i : (Fin (n+2) → ℕ) × Perm n) :
    basis n i = rightBasisElement i := Basis.mk_apply _ _ _

theorem expansion_unique (c d : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ)
    (h : c.sum (fun i a => a • rightBasisElement i) =
      d.sum (fun i a => a • rightBasisElement i)) : c = d :=
  (rightBasisElement_linearIndependent n).finsuppLinearCombination_injective h

theorem existsUnique_expansion (x : Presented n) :
    ∃! c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ,
      c.sum (fun i a => a • rightBasisElement i) = x := by
  obtain ⟨c,hc⟩ := exists_expansion x
  exact ⟨c,hc,fun d hd => expansion_unique d c (hd.trans hc.symm)⟩

/-- The dot monomial acts FIRST; the divided-difference word acts afterwards. -/
def rightOperator (i : (Fin (n+2) → ℕ) × Perm n) :
    Module.End ℤ (SkewPolynomial (n+2)) :=
  dividedElementOperator i.2 * LinearMap.mulLeft ℤ (monomial i.1 1)

@[simp] theorem rightOperator_apply (i : (Fin (n+2) → ℕ) × Perm n)
    (f : SkewPolynomial (n+2)) :
    rightOperator i f = dividedElementOperator i.2 (monomial i.1 1 * f) := rfl

theorem action_rightBasisElement (i : (Fin (n+2) → ℕ) × Perm n) :
    action n (rightBasisElement i) = rightOperator i := by
  apply LinearMap.ext
  intro f
  rw [rightBasisElement, action_mul_apply, NilHeckeBasis.action_dotMonomial]
  rfl

theorem action_rightBasisElement_apply (i : (Fin (n+2) → ℕ) × Perm n)
    (f : SkewPolynomial (n+2)) :
    action n (rightBasisElement i) f = dividedElementOperator i.2 (monomial i.1 1 * f) := by
  rw [action_rightBasisElement, rightOperator_apply]

/-- Integral form of the RIGHT operator-independence claim in Proposition 2.11. -/
theorem rightOperator_linearIndependent (n : ℕ) : LinearIndependent ℤ (@rightOperator n) := by
  let a : Presented n →ₗ[ℤ] Module.End ℤ (SkewPolynomial (n+2)) :=
    { toFun := action n
      map_add' := map_add _
      map_smul' := by intros; exact map_zsmul _ _ _ }
  have h := (rightBasisElement_linearIndependent n).map' a
    (LinearMap.ker_eq_bot.mpr (NilHeckeBasis.action_injective n))
  simpa only [Function.comp_def, show ∀ x, a x = action n x from fun _ => rfl,
    action_rightBasisElement] using h

theorem right_relation_coefficients (s : Finset ((Fin (n+2) → ℕ) × Perm n))
    (c : ((Fin (n+2) → ℕ) × Perm n) → ℤ)
    (h : ∀ f : SkewPolynomial (n+2), ∑ i ∈ s,
      c i • dividedElementOperator i.2 (monomial i.1 1 * f) = 0) :
    ∀ i ∈ s, c i = 0 := by
  apply linearIndependent_iff'.mp (rightOperator_linearIndependent n) s c
  apply LinearMap.ext
  intro f
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    rightOperator_apply] using h f

end
end OddMath.Frontier.NilHeckeRightBasis
