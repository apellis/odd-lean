import OddMath.Frontier.StaircaseSpanning
import OddMath.Frontier.ElementaryBasis
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Integral right staircase independence
EKL arXiv:1111.1320v1 pp.12–13, (2.46) and the right-hand version of
Proposition 2.13's multiplication map. Reuses EXACT StaircaseSpanning.StairIndex,
stairMonomial, ElementaryBranching.E and right_span, with coefficients on the RIGHT.

The proof projects to actual homogeneous integer polynomial pieces. An explicit
first-minimum insertion injects staircase/partition pairs into monomial indices
without assuming a Hilbert series. Source spanning gives integral surjectivity in
each degree; Orzech's finite Noetherian module theorem supplies injectivity over
ℤ. Cardinal equality is then a consequence of the resulting integral isomorphism.
Ranks 0 and 1 are proved directly, and ranks n+2 specialize to the actual common
kernel. This does not identify the staircase basis with Schubert polynomials,
prove left freeness, or assert faithfulness/End or all of Proposition 2.13. -/
namespace OddMath.Frontier.StaircaseIndependence
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open StaircaseSpanning ElementaryBranching ElementaryGeneration ElementaryBasis
open scoped BigOperators
noncomputable section

/-- The actual polynomial degree projection, with integer coefficients unchanged. -/
def grade {N : ℕ} (d : ℕ) : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N :=
  { Finsupp.filterAddHom (fun a => weight a = d) with
    map_smul' := by intro z f; exact Finsupp.filter_smul }

@[simp] theorem grade_apply {N : ℕ} (d : ℕ) (f : SkewPolynomial N) (a : Exp N) :
    grade d f a = if weight a = d then f a else 0 := by
  classical
  exact Finsupp.filter_apply (fun a => weight a = d) f a

theorem grade_homogeneous {N : ℕ} (d : ℕ) (f : SkewPolynomial N) :
    Homogeneous d (grade d f) := by
  intro a ha
  simp [ha]

theorem grade_of_homogeneous {N d : ℕ} {f : SkewPolynomial N}
    (hf : Homogeneous d f) (e : ℕ) : grade e f = if d = e then f else 0 := by
  classical
  ext a
  by_cases hde : d = e
  · subst e
    by_cases ha : weight a = d
    · simp [ha]
    · simp [ha, hf a ha]
  · by_cases ha : weight a = e
    · have had : weight a ≠ d := by omega
      simp [hde, ha, hf a had]
    · simp [hde, ha]

theorem grade_ext {N : ℕ} {f g : SkewPolynomial N}
    (h : ∀ d, grade d f = grade d g) : f = g := by
  ext a
  have hh := congrArg (fun p : SkewPolynomial N => p a) (h (weight a))
  simpa using hh

/-- Multiplication by a fixed monomial shifts the actual degree projection. -/
theorem grade_monomial_mul {N : ℕ} (a : Exp N) (f : SkewPolynomial N) (d : ℕ) :
    grade d (monomial a 1 * f) =
      if weight a ≤ d then monomial a 1 * grade (d-weight a) f else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [mul_add, map_add, hf, hg]
    split_ifs <;> simp
  | single b z =>
    change grade d (monomial a 1 * monomial b z) =
      if weight a ≤ d then monomial a 1 * grade (d-weight a) (monomial b z) else 0
    have hm : monomial a 1 * monomial b z = monomial (a+b) (1*z*OddMath.skewSign a b) :=
      OddMath.SkewPolynomial.mul_monomial _ _ _ _
    rw [hm, grade_of_homogeneous (homogeneous_monomial _ _),
      grade_of_homogeneous (homogeneous_monomial _ _)]
    have hw : weight (a+b) = weight a + weight b := by
      simp only [weight, Pi.add_apply, Finset.sum_add_distrib]
    by_cases ha : weight a ≤ d
    · rw [if_pos ha]
      by_cases hb : weight b = d-weight a
      · rw [if_pos hb, if_pos (by omega), hm]
      · rw [if_neg hb, if_neg (by omega), mul_zero]
    · rw [if_neg ha, if_neg (by omega)]

/-- Each literal elementary word belongs to the assigned elementary subring. -/
theorem word_mem_E (N : ℕ) (w : List ℕ) : elementaryWord N w ∈ E N := by
  induction w with
  | nil => exact (E N).one_mem
  | cons k w ih => exact (E N).mul_mem (Subring.subset_closure ⟨k,rfl⟩) ih

theorem word_append (N : ℕ) (u v : List ℕ) :
    elementaryWord N (u++v) = elementaryWord N u * elementaryWord N v := by
  simp [elementaryWord, List.map_append, List.prod_append]

/-- The integer span of actual words, used only to justify graded projection. -/
theorem E_le_word_span (N : ℕ) (f : SkewPolynomial N) (hf : f ∈ E N) :
    f ∈ Submodule.span ℤ (Set.range (elementaryWord N)) := by
  let S := Submodule.span ℤ (Set.range (elementaryWord N))
  have hm : ∀ f ∈ S, ∀ g ∈ S, f*g ∈ S := by
    intro f hf g hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨u,rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨v,rfl⟩ := hg
        exact Submodule.subset_span ⟨u++v, word_append N u v⟩
      | zero => simpa only [mul_zero, zero_mul] using S.zero_mem
      | add g h _ _ hg hh => simpa [mul_add] using S.add_mem hg hh
      | smul z g _ hg => simpa only [mul_smul_comm] using S.smul_mem z hg
    | zero => simpa only [mul_zero, zero_mul] using S.zero_mem
    | add f h _ _ hf hh => simpa [add_mul] using S.add_mem hf hh
    | smul z f _ hf => simpa only [smul_mul_assoc] using S.smul_mem z hf
  induction hf using Subring.closure_induction with
  | mem f hf =>
    obtain ⟨k,rfl⟩ := hf
    exact Submodule.subset_span ⟨[k], by simp [elementaryWord]⟩
  | zero => exact S.zero_mem
  | one => exact Submodule.subset_span ⟨[],rfl⟩
  | add f g _ _ hf hg => exact S.add_mem hf hg
  | neg f _ hf => exact S.neg_mem hf
  | mul f g _ _ hf hg => exact hm f hf g hg

/-- Grading really restricts to E; it is not an assumed graded-algebra instance. -/
theorem grade_mem_E {N : ℕ} (d : ℕ) (f : SkewPolynomial N) (hf : f ∈ E N) :
    grade d f ∈ E N := by
  have hs := E_le_word_span N f hf
  clear hf
  induction hs using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w,rfl⟩ := hf
    rw [grade_of_homogeneous (word_homogeneous N w)]
    split_ifs
    · exact word_mem_E N w
    · exact (E N).zero_mem
  | zero => simpa using (E N).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using (E N).add_mem hf hg
  | smul z f _ hf => simpa only [map_smul] using (E N).zsmul_mem hf z

/-- Insert the first minimum k at j; predecessors are raised by k+1.
This is only the counting injection needed by the finite integral argument. -/
def insertMin : {N : ℕ} → Fin (N+1) → ℕ → Exp N → Exp (N+1)
  | 0, _, k, _ => fun _ => k
  | _N+1, j, k, b => Fin.cases (Fin.cons k (fun i => b i+k))
      (fun j => Fin.cons (b 0+k+1) (insertMin j k (fun i => b i.succ))) j

theorem insertMin_at {N : ℕ} (j : Fin (N+1)) (k : ℕ) (b : Exp N) :
    insertMin j k b j = k := by
  induction N with
  | zero => rfl
  | succ N ih =>
    cases j using Fin.cases with
    | zero => simp [insertMin]
    | succ j => simpa [insertMin] using ih j (fun i => b i.succ)

theorem insertMin_le {N : ℕ} (j : Fin (N+1)) (k : ℕ) (b : Exp N)
    (i : Fin (N+1)) : k ≤ insertMin j k b i := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    cases j using Fin.cases with
    | zero =>
      cases i using Fin.cases <;> simp [insertMin]
    | succ j =>
      cases i using Fin.cases with
      | zero => simp [insertMin]; omega
      | succ i => simpa [insertMin] using ih j (fun i => b i.succ) i

theorem insertMin_lt_before {N : ℕ} (j : Fin (N+1)) (k : ℕ) (b : Exp N)
    (i : Fin (N+1)) (hi : i < j) : k < insertMin j k b i := by
  induction N with
  | zero => exact False.elim (by have := i.isLt; have := j.isLt; omega)
  | succ N ih =>
    cases j using Fin.cases with
    | zero => simp at hi
    | succ j =>
      cases i using Fin.cases with
      | zero => simp [insertMin]; omega
      | succ i => simpa [insertMin] using ih j (fun i => b i.succ) i (Fin.succ_lt_succ_iff.mp hi)

theorem insertMin_b_injective {N : ℕ} (j : Fin (N+1)) (k : ℕ) :
    Function.Injective (insertMin j k) := by
  induction N with
  | zero => intro b c _; exact Subsingleton.elim _ _
  | succ N ih =>
    cases j using Fin.cases with
    | zero =>
      intro b c h
      funext i
      have hh := congrFun h i.succ
      simp only [insertMin, Fin.cases_zero, Fin.cons_succ] at hh
      omega
    | succ j =>
      intro b c h
      have hzero := congrFun h 0
      simp only [insertMin, Fin.cases_succ, Fin.cons_zero] at hzero
      have ht : (fun i : Fin N => b i.succ) = (fun i : Fin N => c i.succ) := by
        apply ih j
        funext i
        have hh := congrFun h i.succ
        simpa only [insertMin, Fin.cases_succ, Fin.cons_succ] using hh
      funext i
      cases i using Fin.cases with
      | zero => omega
      | succ i => exact congrFun ht i

theorem insertMin_injective {N : ℕ} {j l : Fin (N+1)} {k h : ℕ} {b c : Exp N}
    (he : insertMin j k b = insertMin l h c) : j=l ∧ k=h ∧ b=c := by
  have hkh : k=h := by
    apply le_antisymm
    · have hh := insertMin_le j k b l
      rwa [he, insertMin_at] at hh
    · have hh := insertMin_le l h c j
      rwa [← he, insertMin_at] at hh
  subst h
  have hjl : j=l := by
    apply le_antisymm
    · by_contra hh
      have hx := insertMin_lt_before j k b l (lt_of_not_ge hh)
      rw [he, insertMin_at] at hx
      exact (lt_irrefl _ hx)
    · by_contra hh
      have hx := insertMin_lt_before l k c j (lt_of_not_ge hh)
      rw [← he, insertMin_at] at hx
      exact (lt_irrefl _ hx)
  subst l
  exact ⟨rfl,rfl,insertMin_b_injective j k he⟩

theorem weight_insertMin {N : ℕ} (j : Fin (N+1)) (k : ℕ) (b : Exp N) :
    weight (insertMin j k b) = weight b + (N+1)*k + j.val := by
  induction N with
  | zero => simp [weight, insertMin, Fin.sum_univ_succ]
  | succ N ih =>
    cases j using Fin.cases with
    | zero => simp [insertMin, weight, Fin.sum_univ_succ, Finset.sum_add_distrib]; ring
    | succ j =>
      change (∑ i, Fin.cons (b 0+k+1) (insertMin j k (fun i => b i.succ)) i) = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      change b 0+k+1 + weight (insertMin j k (fun i => b i.succ)) = _
      rw [ih]
      rw [show weight b = b 0 + weight (fun i => b i.succ) from Fin.sum_univ_succ b]
      simp only [Fin.val_succ]
      ring

def tailStair {N : ℕ} (a : StairIndex (N+1)) : StairIndex N :=
  ⟨fun i => a.val i.succ, by
    intro i
    change a.val i.succ ≤ N-1-i.val
    have h := a.property i.succ
    simp only [Fin.val_succ] at h
    omega⟩

def dropPart {N : ℕ} (p : Exp (N+1)) : Exp N := fun i => p i.castSucc - p (Fin.last N)

theorem dropPart_antitone {N : ℕ} {p : Exp (N+1)} (hp : Antitone p) :
    Antitone (dropPart p) := by
  intro i j hij
  exact Nat.sub_le_sub_right (hp (Fin.castSucc_le_castSucc_iff.mpr hij)) _

theorem weight_dropPart {N : ℕ} {p : Exp (N+1)} (hp : Antitone p) :
    weight p = weight (dropPart p) + (N+1)*p (Fin.last N) := by
  have he (i : Fin N) : p i.castSucc = dropPart p i + p (Fin.last N) := by
    exact (Nat.sub_add_cancel (hp (Fin.le_last i.castSucc))).symm
  unfold weight
  rw [Fin.sum_univ_castSucc]
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- Explicit degree-preserving counting injection, not a dimension assumption. -/
def encode : (N : ℕ) → StairIndex N → Exp N → Exp N
  | 0, _, _ => 0
  | N+1, a, p => insertMin ⟨a.val 0, by have h := a.property 0; simp at h; omega⟩
      (p (Fin.last N)) (encode N (tailStair a) (dropPart p))

theorem weight_encode (N : ℕ) (a : StairIndex N) (p : Exp N) (hp : Antitone p) :
    weight (encode N a p) = weight a.val + weight p := by
  induction N with
  | zero => simp [weight]
  | succ N ih =>
    rw [encode, weight_insertMin, ih _ _ (dropPart_antitone hp), weight_dropPart hp]
    have ha : weight a.val = a.val 0 + weight (tailStair a).val := Fin.sum_univ_succ a.val
    rw [ha]
    simp only
    omega

theorem encode_injective (N : ℕ) (a b : StairIndex N) (p q : Exp N)
    (hp : Antitone p) (hq : Antitone q) (he : encode N a p = encode N b q) :
    a=b ∧ p=q := by
  induction N with
  | zero => exact ⟨Subtype.ext (Subsingleton.elim _ _), Subsingleton.elim _ _⟩
  | succ N ih =>
    obtain ⟨hj,hk,ht⟩ := insertMin_injective he
    obtain ⟨ha,hp'⟩ := ih (tailStair a) (tailStair b) (dropPart p) (dropPart q)
      (dropPart_antitone hp) (dropPart_antitone hq) ht
    have hfirst : a.val 0 = b.val 0 := congrArg Fin.val hj
    constructor
    · apply Subtype.ext
      funext i
      cases i using Fin.cases with
      | zero => exact hfirst
      | succ i => exact congrFun (congrArg Subtype.val ha) i
    · funext i
      refine Fin.lastCases hk (fun i => ?_) i
      have hh := congrFun hp' i
      have hpi := hp (Fin.le_last i.castSucc)
      have hqi := hq (Fin.le_last i.castSucc)
      change p i.castSucc - p (Fin.last N) = q i.castSucc - q (Fin.last N) at hh
      omega

/-- Exact homogeneous integer source index of multiplication. -/
abbrev PairIndex (N d : ℕ) :=
  {ap : StairIndex N × Exp N // Antitone ap.2 ∧ weight ap.1.val + weight ap.2 = d}

abbrev MonoIndex (N d : ℕ) := {a : Exp N // weight a = d}

instance monoIndexFinite (N d : ℕ) : Finite (MonoIndex N d) := by
  let enc : MonoIndex N d → (Fin N → Fin (d+1)) := fun a i => ⟨a.val i, by
    have h : a.val i ≤ weight a.val := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [a.property] at h; omega⟩
  apply Finite.of_injective enc
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

instance monoIndexFintype (N d : ℕ) : Fintype (MonoIndex N d) := Fintype.ofFinite _

def indexEncode (N d : ℕ) (a : PairIndex N d) : MonoIndex N d :=
  ⟨encode N a.val.1 a.val.2, (weight_encode N _ _ a.property.1).trans a.property.2⟩

theorem indexEncode_injective (N d : ℕ) : Function.Injective (indexEncode N d) := by
  intro a b h
  have hh := encode_injective N a.val.1 b.val.1 a.val.2 b.val.2 a.property.1 b.property.1
    (congrArg Subtype.val h)
  exact Subtype.ext (Prod.ext hh.1 hh.2)

instance pairIndexFinite (N d : ℕ) : Finite (PairIndex N d) :=
  Finite.of_injective _ (indexEncode_injective N d)
instance pairIndexFintype (N d : ℕ) : Fintype (PairIndex N d) := Fintype.ofFinite _

theorem pair_card_le (N d : ℕ) : Fintype.card (PairIndex N d) ≤ Fintype.card (MonoIndex N d) :=
  Fintype.card_le_of_injective _ (indexEncode_injective N d)

def pairVector (N d : ℕ) (a : PairIndex N d) : SkewPolynomial N :=
  stairMonomial a.val.1 * elementaryWord N (columns a.val.2)

theorem pairVector_homogeneous (N d : ℕ) (a : PairIndex N d) :
    Homogeneous d (pairVector N d a) := by
  have h := homogeneous_mul (homogeneous_monomial a.val.1.val (1:ℤ))
    (columns_homogeneous a.val.2 a.property.1)
  simpa only [a.property.2] using h

/-- The actual degree-d polynomial piece has its finite monomial coordinates. -/
abbrev polyPiece (N d : ℕ) := Finsupp.supported ℤ ℤ {a : Exp N | weight a = d}

theorem mem_polyPiece {N d : ℕ} (f : SkewPolynomial N) :
    f ∈ polyPiece N d ↔ Homogeneous d f := Finsupp.mem_supported' ℤ f

def monoCoords (N d : ℕ) : polyPiece N d ≃ₗ[ℤ] (MonoIndex N d →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

def vectorInPiece (N d : ℕ) (a : PairIndex N d) : polyPiece N d :=
  ⟨pairVector N d a, (mem_polyPiece _).mpr (pairVector_homogeneous N d a)⟩

def mulMap (N d : ℕ) : (PairIndex N d →₀ ℤ) →ₗ[ℤ] (MonoIndex N d →₀ ℤ) :=
  (monoCoords N d).toLinearMap ∘ₗ Finsupp.linearCombination ℤ (vectorInPiece N d)

/-- Integral surjectivity in the SAME degree, extracted from actual right_span. -/
theorem pair_span (n d : ℕ) (f : SkewPolynomial (n+2)) (hf : Homogeneous d f) :
    f ∈ Submodule.span ℤ (Set.range (pairVector (n+2) d)) := by
  classical
  let S := Submodule.span ℤ (Set.range (pairVector (n+2) d))
  obtain ⟨c,hc⟩ := right_span (n+2) f
  have he := congrArg (grade d) hc
  rw [grade_of_homogeneous hf, if_pos rfl, map_sum] at he
  rw [he]
  apply S.sum_mem
  intro a _
  rw [stairMonomial, grade_monomial_mul]
  by_cases ha : weight a.val ≤ d
  · rw [if_pos ha]
    let e := d-weight a.val
    let g : degreePiece n e := ⟨grade e (c a), by
      constructor
      · have hg := grade_mem_E (N := n+2) e (c a : SkewPolynomial (n+2)) (c a).property
        exact (le_of_eq ((E_eq_elementaryClosure n).trans
          (ElementaryGeneration.kernel_eq_elementaryClosure n).symm)) hg
      · exact grade_homogeneous e _⟩
    have hexp : (g : SkewPolynomial (n+2)) = ∑ p : Index (n+2) e,
        ((gradedBasis n e).repr g) p • elementaryWord (n+2) (columns p.val) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, gradedBasis_apply] using
        (congrArg (fun q : degreePiece n e => (q : SkewPolynomial (n+2)))
          ((gradedBasis n e).sum_repr g)).symm
    change monomial a.val 1 * (g : SkewPolynomial (n+2)) ∈ S
    rw [hexp, Finset.mul_sum]
    apply S.sum_mem
    intro p _
    rw [mul_smul_comm]
    apply S.smul_mem
    let ap : PairIndex (n+2) d := ⟨(a,p.val),p.property.1,by
      change weight a.val + weight p.val = d
      have hp := p.property.2
      dsimp [e] at hp
      omega⟩
    exact Submodule.subset_span ⟨ap,rfl⟩
  · rw [if_neg ha]
    exact S.zero_mem

theorem mulMap_surjective (n d : ℕ) : Function.Surjective (mulMap (n+2) d) := by
  intro y
  let f := (monoCoords (n+2) d).symm y
  have hf := pair_span n d f.val ((mem_polyPiece _).mp f.property)
  rw [← Finsupp.range_linearCombination] at hf
  obtain ⟨z,hz⟩ := hf
  refine ⟨z, ?_⟩
  have hh : Finsupp.linearCombination ℤ (vectorInPiece (n+2) d) z = f := by
    apply Subtype.ext
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
      Submodule.coe_smul, vectorInPiece] using hz
  change monoCoords (n+2) d (Finsupp.linearCombination ℤ (vectorInPiece (n+2) d) z) = y
  rw [hh]
  exact (monoCoords (n+2) d).apply_symm_apply y

/-- Integral finite-module injection+surjection, not a rational rank assertion. -/
theorem mulMap_injective (n d : ℕ) : Function.Injective (mulMap (n+2) d) := by
  let i : (PairIndex (n+2) d →₀ ℤ) →ₗ[ℤ] (MonoIndex (n+2) d →₀ ℤ) :=
    Finsupp.lmapDomain ℤ ℤ (indexEncode (n+2) d)
  exact IsNoetherian.injective_of_surjective_of_injective i (mulMap (n+2) d)
    (Finsupp.mapDomain_injective (indexEncode_injective (n+2) d)) (mulMap_surjective n d)

theorem pair_independent (n d : ℕ) : LinearIndependent ℤ (pairVector (n+2) d) := by
  intro x y h
  apply mulMap_injective n d
  apply congrArg (monoCoords (n+2) d)
  apply Subtype.ext
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
    Submodule.coe_smul, vectorInPiece] using h

theorem pair_card_eq (n d : ℕ) :
    Fintype.card (PairIndex (n+2) d) = Fintype.card (MonoIndex (n+2) d) := by
  have h := (LinearEquiv.ofBijective (mulMap (n+2) d)
    ⟨mulMap_injective n d, mulMap_surjective n d⟩).finrank_eq
  simpa only [Module.finrank_finsupp_self] using h

abbrev ActiveStair (N d : ℕ) := {a : StairIndex N // weight a.val ≤ d}
abbrev SigmaIndex (N d : ℕ) := (a : ActiveStair N d) × Index N (d-weight a.val.val)

def sigmaPair (N d : ℕ) (x : SigmaIndex N d) : PairIndex N d :=
  ⟨(x.1.val,x.2.val),x.2.property.1,by
    change weight x.1.val.val + weight x.2.val = d
    have ha := x.1.property
    have hp := x.2.property.2
    omega⟩

theorem sigmaPair_injective (N d : ℕ) : Function.Injective (sigmaPair N d) := by
  rintro ⟨a,p⟩ ⟨b,q⟩ h
  have hab : a=b := Subtype.ext (congrArg (fun x : PairIndex N d => x.val.1) h)
  subst b
  have hpq : p=q := Subtype.ext (congrArg (fun x : PairIndex N d => x.val.2) h)
  subst q
  rfl

def coeffPiece (n e : ℕ) (c : E (n+2)) : degreePiece n e :=
  ⟨grade e (c : SkewPolynomial (n+2)), by
    constructor
    · exact (le_of_eq ((E_eq_elementaryClosure n).trans
        (ElementaryGeneration.kernel_eq_elementaryClosure n).symm))
        (grade_mem_E e (c : SkewPolynomial (n+2)) c.property)
    · exact grade_homogeneous e _⟩

theorem coeffPiece_expand (n e : ℕ) (c : E (n+2)) :
    grade e (c : SkewPolynomial (n+2)) = ∑ p : Index (n+2) e,
      ((gradedBasis n e).repr (coeffPiece n e c)) p • elementaryWord (n+2) (columns p.val) := by
  simpa only [Submodule.coe_sum, Submodule.coe_smul, gradedBasis_apply] using
    (congrArg (fun q : degreePiece n e => (q : SkewPolynomial (n+2)))
      ((gradedBasis n e).sum_repr (coeffPiece n e c))).symm

/-- All homogeneous coefficients vanish, not merely a rational image. -/
theorem graded_coeff_zero (n d : ℕ) (c : StairIndex (n+2) → E (n+2))
    (hc : (∑ a, stairMonomial a * (c a : SkewPolynomial (n+2))) = 0)
    (a : StairIndex (n+2)) (ha : weight a.val ≤ d) :
    grade (d-weight a.val) (c a : SkewPolynomial (n+2)) = 0 := by
  classical
  let z (x : SigmaIndex (n+2) d) : ℤ :=
    ((gradedBasis n (d-weight x.1.val.val)).repr
      (coeffPiece n (d-weight x.1.val.val) (c x.1.val))) x.2
  have hlin := (pair_independent n d).comp (sigmaPair (n+2) d) (sigmaPair_injective (n+2) d)
  have hz : ∑ x : SigmaIndex (n+2) d,
      z x • pairVector (n+2) d (sigmaPair (n+2) d x) = 0 := by
    rw [Fintype.sum_sigma]
    have hexp (b : ActiveStair (n+2) d) :
        (∑ p : Index (n+2) (d-weight b.val.val),
          z ⟨b,p⟩ • pairVector (n+2) d (sigmaPair (n+2) d ⟨b,p⟩)) =
        stairMonomial b.val * grade (d-weight b.val.val) (c b.val : SkewPolynomial (n+2)) := by
      rw [coeffPiece_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact (mul_smul_comm _ _ _).symm
    simp_rw [hexp]
    have hg := congrArg (grade d) hc
    rw [map_sum, map_zero] at hg
    simp_rw [stairMonomial, grade_monomial_mul] at hg
    rw [← Finset.sum_filter] at hg
    rw [Finset.sum_subtype (p := fun b : StairIndex (n+2) => weight b.val ≤ d)
      _ (fun b => by simp) _] at hg
    exact hg
  have hzall : ∀ x, z x=0 := by
    intro x
    exact (linearIndependent_iff'.mp hlin) Finset.univ z hz x (Finset.mem_univ x)
  rw [coeffPiece_expand]
  apply Finset.sum_eq_zero
  intro p _
  have hh := hzall (⟨⟨a,ha⟩,p⟩ : SigmaIndex (n+2) d)
  change ((gradedBasis n (d-weight a.val)).repr (coeffPiece n (d-weight a.val) (c a))) p = 0 at hh
  rw [hh, zero_smul]

/-- Literal integral right coefficient uniqueness, for N≥2. -/
theorem right_coeff_zero_ge_two (n : ℕ) (c : StairIndex (n+2) → E (n+2))
    (hc : (∑ a, stairMonomial a * (c a : SkewPolynomial (n+2))) = 0) :
    ∀ a, c a = 0 := by
  intro a
  apply Subtype.ext
  apply grade_ext
  intro e
  have h := graded_coeff_zero n (e+weight a.val) c hc a (by omega)
  simpa only [Nat.add_sub_cancel, map_zero, Subring.coe_zero] using h

theorem small_stair_zero {N : ℕ} (hN : N ≤ 1) (a : StairIndex N) : a.val = 0 := by
  funext i
  have hi := a.property i
  change a.val i = 0
  omega

theorem right_coeff_zero_small {N : ℕ} (hN : N ≤ 1)
    (c : StairIndex N → E N)
    (hc : (∑ a, stairMonomial a * (c a : SkewPolynomial N)) = 0) :
    ∀ a, c a = 0 := by
  classical
  have hsub : Subsingleton (StairIndex N) := ⟨fun a b =>
    Subtype.ext ((small_stair_zero hN a).trans (small_stair_zero hN b).symm)⟩
  intro a
  have he : (∑ b, stairMonomial b * (c b : SkewPolynomial N)) = (c a : SkewPolynomial N) := by
    rw [Finset.sum_eq_single a]
    · rw [stairMonomial, small_stair_zero hN a]
      exact one_mul _
    · intro b _ hba
      exact False.elim (hba (hsub.elim b a))
    · intro h
      exact False.elim (h (Finset.mem_univ a))
  apply Subtype.ext
  exact he.symm.trans hc

/-- Every rank, including 0: the literal finite right-coefficient relation. -/
theorem right_coeff_zero (N : ℕ) (c : StairIndex N → E N)
    (hc : (∑ a, stairMonomial a * (c a : SkewPolynomial N)) = 0) :
    ∀ a, c a = 0 := by
  cases N with
  | zero => exact right_coeff_zero_small (by omega) c hc
  | succ N =>
    cases N with
    | zero => exact right_coeff_zero_small (by omega) c hc
    | succ n => exact right_coeff_zero_ge_two n c hc

theorem right_coeff_unique (N : ℕ) (c b : StairIndex N → E N)
    (h : (∑ a, stairMonomial a * (c a : SkewPolynomial N)) =
      ∑ a, stairMonomial a * (b a : SkewPolynomial N)) : c=b := by
  have hz : (∑ a, stairMonomial a * ((c a - b a : E N) : SkewPolynomial N)) = 0 := by
    change (∑ a, stairMonomial a * ((c a : SkewPolynomial N) - (b a : SkewPolynomial N))) = 0
    simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]
  have hh := right_coeff_zero N (fun a => c a - b a) hz
  funext a
  exact sub_eq_zero.mp (hh a)

/-- Actual right staircase decomposition: existence and uniqueness over integers. -/
theorem right_decomposition_unique (N : ℕ) (f : SkewPolynomial N) :
    ∃! c : StairIndex N → E N, f = ∑ a, stairMonomial a * (c a : SkewPolynomial N) := by
  obtain ⟨c,hc⟩ := right_span N f
  refine ⟨c,hc,?_⟩
  intro b hb
  exact right_coeff_unique N b c (hb.symm.trans hc)

theorem E_eq_kernel (n : ℕ) : E (n+2) = OddSymmetricKernel.kernelSubring n :=
  (E_eq_elementaryClosure n).trans (ElementaryGeneration.kernel_eq_elementaryClosure n).symm

/-- The coefficients belong to the ACTUAL common kernel, not a replacement ring. -/
theorem right_kernel_coeff_zero (n : ℕ)
    (c : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n)
    (hc : (∑ a, stairMonomial a * (c a : SkewPolynomial (n+2))) = 0) :
    ∀ a, c a = 0 := by
  let b : StairIndex (n+2) → E (n+2) := fun a => ⟨c a,
    (le_of_eq (E_eq_kernel n).symm) (c a).property⟩
  have hh := right_coeff_zero (n+2) b hc
  intro a
  apply Subtype.ext
  exact congrArg (fun x : E (n+2) => (x : SkewPolynomial (n+2))) (hh a)

theorem right_kernel_decomposition_unique (n : ℕ) (f : SkewPolynomial (n+2)) :
    ∃! c : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n,
      f = ∑ a, stairMonomial a * (c a : SkewPolynomial (n+2)) := by
  rw [← E_eq_kernel]
  exact right_decomposition_unique (n+2) f

end
end OddMath.Frontier.StaircaseIndependence
