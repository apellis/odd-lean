import OddMath.Frontier.NilHeckeRightBasis
import OddMath.Frontier.NilCoxeterPresentation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Intervals

/-! EKL1111.1320v1 §2.2: integer source-word grading on the actual quotients.
All constructions below serve Proposition 2.11; N=n+2 throughout. -/
namespace OddMath.Frontier.NilHeckeGrading
open NilHeckeAction NilCoxeterWords NilHeckeBasis
open scoped BigOperators
noncomputable section
variable {n : ℕ}

abbrev Letter (n : ℕ) := Fin (n+2) ⊕ Fin (n+1)
def letterDegree : Letter n → ℤ := Sum.elim (fun _ => 2) (fun _ => -2)
def letterValue : Letter n → Presented n := Sum.elim (dot n) (crossing n)
def wordDegree (w : List (Letter n)) : ℤ := (w.map letterDegree).sum
def wordValue (w : List (Letter n)) : Presented n := (w.map letterValue).prod
/-- Literal word in the source free algebra, before passing to the quotient. -/
def freeWord (w : List (Letter n)) : Free n := (w.map (FreeAlgebra.ι ℤ)).prod

theorem wordValue_eq_image (w : List (Letter n)) :
    wordValue w = quotientMap n (freeWord w) := by
  induction w with
  | nil => simp [wordValue, freeWord]
  | cons g w ih =>
    simp only [wordValue, freeWord, List.map_cons, List.prod_cons, map_mul] at *
    rw [ih]
    cases g <;> rfl

@[simp] theorem wordDegree_append (u v : List (Letter n)) :
    wordDegree (u++v) = wordDegree u + wordDegree v := by simp [wordDegree]
@[simp] theorem wordValue_append (u v : List (Letter n)) :
    wordValue (u++v) = wordValue u * wordValue v := by simp [wordValue]

/-- Source-defined, not a grading imposed on a PBW carrier. -/
def degreePiece (n : ℕ) (d : ℤ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (wordValue '' {w : List (Letter n) | wordDegree w = d})
theorem word_mem (w : List (Letter n)) : wordValue w ∈ degreePiece n (wordDegree w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

theorem degreePiece_mul {a b : ℤ} {x y : Presented n}
    (hx : x ∈ degreePiece n a) (hy : y ∈ degreePiece n b) :
    x*y ∈ degreePiece n (a+b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      rw [← wordValue_append]
      exact Submodule.subset_span ⟨u++v, by change wordDegree (u++v)=a+b; rw [wordDegree_append, hu, hv], rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using (degreePiece n (a+b)).add_mem hx hy
    | smul r x _ hx => simpa only [mul_smul_comm] using (degreePiece n (a+b)).smul_mem r hx
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using (degreePiece n (a+b)).add_mem hx hy
  | smul r x _ hx => simpa only [smul_mul_assoc] using (degreePiece n (a+b)).smul_mem r hx

theorem unit_mem : (1 : Presented n) ∈ degreePiece n 0 := word_mem []
theorem dot_mem (i : Fin (n+2)) : dot n i ∈ degreePiece n 2 := by
  simpa [wordValue, wordDegree, letterValue, letterDegree] using word_mem [Sum.inl i]
theorem crossing_mem (i : Fin (n+1)) : crossing n i ∈ degreePiece n (-2) := by
  simpa [wordValue, wordDegree, letterValue, letterDegree] using word_mem [Sum.inr i]

/-- Mixed-word normalization retains the signed word degree. -/
def mixedPiece (n : ℕ) (d : ℤ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ ((fun vw : List (Fin (n+2)) × Word n => dotWord vw.1 * product vw.2) ''
    {vw | 2*(vw.1.length : ℤ)-2*(vw.2.length : ℤ)=d})
theorem mixed_mem (v : List (Fin (n+2))) (w : Word n) :
    dotWord v * product w ∈ mixedPiece n (2*(v.length : ℤ)-2*(w.length : ℤ)) :=
  Submodule.subset_span ⟨(v,w), rfl, rfl⟩

theorem dot_mul_mixed (j : Fin (n+2)) {d : ℤ} {x : Presented n}
    (hx : x ∈ mixedPiece n d) : dot n j * x ∈ mixedPiece n (2+d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨v,w⟩, hvw, rfl⟩ := hx
    have he : 2*((j::v).length : ℤ)-2*(w.length : ℤ)=2+d := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; change 2*(v.length : ℤ)-2*(w.length : ℤ)=d at hvw; omega
    simpa only [he, dotWord_cons, mul_assoc] using mixed_mem (j::v) w
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using (mixedPiece n (2+d)).add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using (mixedPiece n (2+d)).smul_mem r hx

theorem crossing_mixed (i : Fin (n+1)) (v : List (Fin (n+2))) (w : Word n) :
    crossing n i * (dotWord v * product w) ∈
      mixedPiece n (-2+(2*(v.length : ℤ)-2*(w.length : ℤ))) := by
  induction v with
  | nil =>
    simpa [dotWord, product, List.length_cons, sub_eq_add_neg, mul_add, add_comm, add_left_comm,
      add_assoc] using mixed_mem [] (i::w)
  | cons j v ih =>
    have he : -2+(2*((j::v).length : ℤ)-2*(w.length : ℤ)) =
        2*(v.length : ℤ)-2*(w.length : ℤ) := by simp; omega
    rw [he, dotWord_cons, mul_assoc (dot n j), ← mul_assoc (crossing n i)]
    have ht' (k : Fin (n+2)) : dot n k * (crossing n i * (dotWord v * product w)) ∈
        mixedPiece n (2*(v.length : ℤ)-2*(w.length : ℤ)) := by
      convert dot_mul_mixed k ih using 1
      congr 1
      omega
    by_cases hl : j = i.castSucc
    · subst j
      rw [crossing_dot_left, sub_mul, one_mul, mul_assoc]
      exact (mixedPiece n _).sub_mem (mixed_mem v w) (ht' _)
    · by_cases hr : j = i.succ
      · subst j
        rw [crossing_dot_right, sub_mul, one_mul, mul_assoc]
        exact (mixedPiece n _).sub_mem (mixed_mem v w) (ht' _)
      · rw [crossing_dot_other i j hl hr, neg_mul, mul_assoc]
        exact (mixedPiece n _).neg_mem (ht' _)

theorem crossing_mul_mixed (i : Fin (n+1)) {d : ℤ} {x : Presented n}
    (hx : x ∈ mixedPiece n d) : crossing n i * x ∈ mixedPiece n (-2+d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨v,w⟩, hvw, rfl⟩ := hx
    simpa only [show 2*(v.length : ℤ)-2*(w.length : ℤ)=d from hvw] using crossing_mixed i v w
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using (mixedPiece n (-2+d)).add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using (mixedPiece n (-2+d)).smul_mem r hx

theorem word_mem_mixed (w : List (Letter n)) : wordValue w ∈ mixedPiece n (wordDegree w) := by
  induction w with
  | nil => simpa [wordValue, wordDegree, dotWord, product] using mixed_mem (n:=n) [] []
  | cons g w ih =>
    cases g with
    | inl j => simpa [wordValue, wordDegree, letterValue, letterDegree] using dot_mul_mixed j ih
    | inr i => simpa [wordValue, wordDegree, letterValue, letterDegree] using crossing_mul_mixed i ih

abbrev Index (n : ℕ) := (Fin (n+2) → ℕ) × Perm n
def weight (i : Index n) : ℤ := 2*(∑ j, i.1 j : ℕ)-2*(length i.2 : ℤ)
abbrev DegreeIndex (n : ℕ) (d : ℤ) := {i : Index n // weight i = d}
def leftPiece (n : ℕ) (d : ℤ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (fun i : DegreeIndex n d => basisElement i.val))

theorem sum_count (v : List (Fin (n+2))) : ∑ j, v.count j = v.length := by
  induction v with
  | nil => simp
  | cons j v ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    simp [ih]

theorem mixed_mem_left (v : List (Fin (n+2))) (w : Word n) :
    dotWord v * product w ∈ leftPiece n (2*(v.length : ℤ)-2*(w.length : ℤ)) := by
  rw [dotWord_normalize, smul_mul_assoc]
  apply Submodule.smul_mem
  by_cases hw : Reduced w
  · have hi : weight ((fun j => v.count j), permutation w) =
        2*(v.length : ℤ)-2*(w.length : ℤ) := by
      simp only [weight, sum_count]
      rw [← hw]
    have hm : basisElement ((fun j => v.count j), permutation w) ∈
        leftPiece n (2*(v.length : ℤ)-2*(w.length : ℤ)) :=
      Submodule.subset_span ⟨⟨_,hi⟩, rfl⟩
    rcases reduced_dividedElement w hw with h | h
    · rw [h]; exact hm
    · rw [h, mul_neg]; exact Submodule.neg_mem _ hm
  · rw [nonreduced_zero w hw, mul_zero]; exact Submodule.zero_mem _

theorem degreePiece_le_leftPiece (d : ℤ) : degreePiece n d ≤ leftPiece n d := by
  have hm : mixedPiece n d ≤ leftPiece n d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨v,w⟩,h,rfl⟩
    simpa only [show 2*(v.length : ℤ)-2*(w.length : ℤ)=d from h] using mixed_mem_left v w
  apply Submodule.span_le.mpr
  rintro _ ⟨w,h,rfl⟩
  exact hm (by simpa only [show wordDegree w = d from h] using word_mem_mixed w)

theorem dotWord_mem (v : List (Fin (n+2))) :
    dotWord v ∈ degreePiece n (2*(v.length : ℤ)) := by
  induction v with
  | nil => exact unit_mem
  | cons j v ih =>
    have h := degreePiece_mul (dot_mem j) ih
    convert h using 1
    congr 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem product_mem (w : Word n) : product w ∈ degreePiece n (-2*(w.length : ℤ)) := by
  induction w with
  | nil => exact unit_mem
  | cons i w ih =>
    have h := degreePiece_mul (crossing_mem i) ih
    convert h using 1
    congr 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem dotMonomial_mem (A : Fin (n+2) → ℕ) :
    dotMonomial A ∈ degreePiece n (2*(∑ j, A j : ℕ)) := by
  have hl : (PbwNormalization.canonicalWord A).length = ∑ j, A j := by
    rw [← sum_count]
    simp only [PbwNormalization.canonicalWord_count]
  simpa only [dotWord_canonical, hl] using dotWord_mem (PbwNormalization.canonicalWord A)

theorem dividedElement_mem (w : Perm n) :
    dividedElement w ∈ degreePiece n (-2*(length w : ℤ)) := by
  simpa only [chosenWord_length] using product_mem (chosenWord w)

theorem basisElement_mem (i : Index n) : basisElement i ∈ degreePiece n (weight i) := by
  simpa only [weight, basisElement, sub_eq_add_neg, neg_mul] using
    degreePiece_mul (dotMonomial_mem i.1) (dividedElement_mem i.2)

theorem degreePiece_eq_leftPiece (n : ℕ) (d : ℤ) : degreePiece n d = leftPiece n d := by
  apply le_antisymm (degreePiece_le_leftPiece d)
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  simpa only [i.property] using basisElement_mem i.val

def rightPiece (n : ℕ) (d : ℤ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (fun i : DegreeIndex n d => NilHeckeRightBasis.rightBasisElement i.val))

theorem reverse_word (w : List (Letter n)) :
    NilHeckeRightBasis.reverseLinear n (wordValue w) = wordValue w.reverse := by
  induction w with
  | nil => simp [wordValue]
  | cons g w ih =>
    have hg : NilHeckeRightBasis.reverseLinear n (letterValue g) = letterValue g := by
      cases g <;> simp [letterValue]
    simpa only [wordValue, List.map_cons, List.prod_cons, NilHeckeRightBasis.reverse_mul,
      hg, List.reverse_cons, wordValue_append, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, List.map_nil, List.prod_nil, mul_one] using congrArg (· * letterValue g) ih

theorem reverse_mem {d : ℤ} {x : Presented n} (hx : x ∈ degreePiece n d) :
    NilHeckeRightBasis.reverseLinear n x ∈ degreePiece n d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    rw [reverse_word]
    exact Submodule.subset_span ⟨w.reverse, by simpa [wordDegree] using hw, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (degreePiece n d).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (degreePiece n d).smul_mem r hx

theorem reverse_left_mem_right {d : ℤ} {x : Presented n} (hx : x ∈ leftPiece n d) :
    NilHeckeRightBasis.reverseLinear n x ∈ rightPiece n d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    obtain ⟨ε,he⟩ := NilHeckeRightBasis.reverse_left_unit i.val
    rw [he]
    change (ε : ℤ) • NilHeckeRightBasis.rightBasisElement (i.val.1, i.val.2⁻¹) ∈ _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨(i.val.1, i.val.2⁻¹), by
      simpa only [weight, OddSchubertAction.length_inv] using i.property⟩, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (rightPiece n d).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (rightPiece n d).smul_mem r hx

theorem degreePiece_eq_rightPiece (n : ℕ) (d : ℤ) : degreePiece n d = rightPiece n d := by
  apply le_antisymm
  · intro x hx
    have hr := reverse_mem hx
    rw [degreePiece_eq_leftPiece] at hr
    simpa only [NilHeckeRightBasis.reverse_involutive n x] using reverse_left_mem_right hr
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hm := degreePiece_mul (dividedElement_mem i.val.2) (dotMonomial_mem i.val.1)
    have he : -2*(length i.val.2 : ℤ) + 2*(∑ j, i.val.1 j : ℕ) = d := by
      calc
        _ = weight i.val := by unfold weight; ring
        _ = d := i.property
    rw [he] at hm
    exact hm

/-- Literal restrictions of the integral bases to the actual source degree piece. -/
def degreeLeftBasis (n : ℕ) (d : ℤ) : Basis (DegreeIndex n d) ℤ (degreePiece n d) :=
  (Basis.span ((basisElement_linearIndependent n).comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degreePiece_eq_leftPiece n d).symm)
def degreeRightBasis (n : ℕ) (d : ℤ) : Basis (DegreeIndex n d) ℤ (degreePiece n d) :=
  (Basis.span ((NilHeckeRightBasis.rightBasisElement_linearIndependent n).comp
    Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degreePiece_eq_rightPiece n d).symm)

@[simp] theorem degreeLeftBasis_apply (d : ℤ) (i : DegreeIndex n d) :
    (degreeLeftBasis n d i : Presented n) = basisElement i.val := by
  simp only [degreeLeftBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  rfl
@[simp] theorem degreeRightBasis_apply (d : ℤ) (i : DegreeIndex n d) :
    (degreeRightBasis n d i : Presented n) = NilHeckeRightBasis.rightBasisElement i.val := by
  simp only [degreeRightBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  rfl

namespace ONC
abbrev Q (n : ℕ) := NilCoxeterPresentation.Presented n
abbrev evalWord {n : ℕ} := @NilCoxeterPresentation.product n
/-- Separate free-crossing presentation, not a subring renamed as ONC. -/
def freeWord (w : Word n) : NilCoxeterPresentation.Free n :=
  (w.map (NilCoxeterPresentation.crossingFree n)).prod
theorem evalWord_eq_image (w : Word n) :
    evalWord w = NilCoxeterPresentation.quotientMap n (freeWord w) := by
  induction w with
  | nil => simp [evalWord, NilCoxeterPresentation.product, freeWord]
  | cons i w ih =>
    simp only [evalWord, NilCoxeterPresentation.product, freeWord, List.map_cons,
      List.prod_cons, map_mul] at *
    rw [ih]
    rfl

def degreePiece (n : ℕ) (d : ℤ) : Submodule ℤ (Q n) :=
  Submodule.span ℤ (evalWord '' {w : Word n | -2*(w.length : ℤ)=d})
def weight (w : Perm n) : ℤ := -2*(length w : ℤ)
abbrev DegreeIndex (n : ℕ) (d : ℤ) := {w : Perm n // weight w = d}
def basisPiece (n : ℕ) (d : ℤ) : Submodule ℤ (Q n) :=
  Submodule.span ℤ (Set.range (fun w : DegreeIndex n d => NilCoxeterPresentation.dividedElement w.val))
theorem word_mem (w : Word n) : evalWord w ∈ degreePiece n (-2*(w.length : ℤ)) :=
  Submodule.subset_span ⟨w,rfl,rfl⟩
theorem unit_mem : (1 : Q n) ∈ degreePiece n 0 := word_mem []

theorem degreePiece_mul {a b : ℤ} {x y : Q n}
    (hx : x ∈ degreePiece n a) (hy : y ∈ degreePiece n b) :
    x*y ∈ degreePiece n (a+b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,hu,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v,hv,rfl⟩ := hy
      rw [← NilCoxeterPresentation.product_append]
      apply Submodule.subset_span
      refine ⟨u++v,?_,rfl⟩
      change -2*(u.length : ℤ)=a at hu
      change -2*(v.length : ℤ)=b at hv
      simp only [Set.mem_setOf_eq, List.length_append, Nat.cast_add]
      omega
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using (degreePiece n (a+b)).add_mem hx hy
    | smul r x _ hx => simpa only [mul_smul_comm] using (degreePiece n (a+b)).smul_mem r hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_mul] using (degreePiece n (a+b)).add_mem hx hy
  | smul r x _ hx => simpa only [smul_mul_assoc] using (degreePiece n (a+b)).smul_mem r hx

theorem divided_mem (w : Perm n) : NilCoxeterPresentation.dividedElement w ∈ degreePiece n (weight w) := by
  simpa only [chosenWord_length, weight] using word_mem (chosenWord w)

theorem degreePiece_eq_basisPiece (n : ℕ) (d : ℤ) : degreePiece n d = basisPiece n d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,hw,rfl⟩
    change NilCoxeterPresentation.product w ∈ basisPiece n d
    by_cases hr : Reduced w
    · have hi : weight (permutation w) = d := by
        unfold weight
        rw [← hr]
        exact hw
      have hm : NilCoxeterPresentation.dividedElement (permutation w) ∈ basisPiece n d :=
        Submodule.subset_span ⟨⟨_,hi⟩,rfl⟩
      rcases NilCoxeterPresentation.reduced_dividedElement w hr with h | h
      · rw [h]; exact hm
      · rw [h]; exact Submodule.neg_mem _ hm
    · rw [NilCoxeterPresentation.nonreduced_zero w hr]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    simpa only [w.property] using divided_mem w.val

def degreeBasis (n : ℕ) (d : ℤ) : Basis (DegreeIndex n d) ℤ (degreePiece n d) :=
  (Basis.span ((NilCoxeterPresentation.dividedElement_linearIndependent n).comp
    Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degreePiece_eq_basisPiece n d).symm)
@[simp] theorem degreeBasis_apply (d : ℤ) (w : DegreeIndex n d) :
    (degreeBasis n d w : Q n) = NilCoxeterPresentation.dividedElement w.val := by
  simp only [degreeBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  rfl
instance degree_free (n : ℕ) (d : ℤ) : Module.Free ℤ (degreePiece n d) :=
  Module.Free.of_basis (degreeBasis n d)
instance degree_finite (n : ℕ) (d : ℤ) : Module.Finite ℤ (degreePiece n d) := by
  classical
  exact Module.Finite.of_basis (degreeBasis n d)
theorem degree_finrank (n : ℕ) (d : ℤ) :
    Module.finrank ℤ (degreePiece n d) = Nat.card (DegreeIndex n d) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (degreeBasis n d)
end ONC

/-- The degree decomposition argument used twice in Proposition 2.11. The carrier
is the original module, not a replacement direct-sum algebra. -/
theorem basis_homogeneous_decomposition {I X : Type*} [AddCommGroup X]
    (b : Basis I ℤ X) (wt : I → ℤ) (piece : ℤ → Submodule ℤ X)
    (heq : ∀ d, piece d = Submodule.span ℤ (Set.range (fun i : {i // wt i=d} => b i.val)))
    (x : X) : ∃! f : ℤ →₀ X, (∀ d, f d ∈ piece d) ∧ f.sum (fun _ y => y) = x := by
  classical
  let dec : X →ₗ[ℤ] (ℤ →₀ X) := b.constr ℤ (fun i => Finsupp.single (wt i) (b i))
  let recmp : (ℤ →₀ X) →ₗ[ℤ] X := Finsupp.lsum ℤ (fun _ => LinearMap.id)
  have hdec (i : I) : dec (b i) = Finsupp.single (wt i) (b i) := b.constr_basis ℤ _ i
  have hrecmp (d : ℤ) (y : X) : recmp (Finsupp.single d y) = y := Finsupp.lsum_single _ _ _ _
  have hrd (y : X) : recmp (dec y) = y := by
    have h : recmp.comp dec = LinearMap.id := by
      apply b.ext
      intro i
      change recmp (dec (b i)) = b i
      rw [hdec, hrecmp]
    exact congrArg (fun f : X →ₗ[ℤ] X => f y) h
  have hpiece {d : ℤ} {y : X} (hy : y ∈ piece d) : dec y = Finsupp.single d y := by
    rw [heq] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      rw [hdec, i.property]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz, Finsupp.single_add]
    | smul r y _ hy => simp only [map_smul, hy, Finsupp.smul_single]
  have hmem (y : X) (d : ℤ) : dec y d ∈ piece d := by
    obtain ⟨c,rfl⟩ := b.repr.symm.surjective y
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c e hc he => simpa using (piece d).add_mem hc he
    | single i r =>
      simp only [map_smul, Basis.repr_symm_apply, Finsupp.linearCombination_single]
      rw [hdec, Finsupp.smul_apply]
      apply Submodule.smul_mem
      by_cases h : wt i = d
      · rw [h, Finsupp.single_eq_same, heq]
        exact Submodule.subset_span ⟨⟨i,h⟩,rfl⟩
      · rw [Finsupp.single_eq_of_ne h]
        exact Submodule.zero_mem _
  have hdr (f : ℤ →₀ X) (hf : ∀ d, f d ∈ piece d) : dec (f.sum (fun _ y => y)) = f := by
    simp only [Finsupp.sum, map_sum]
    calc
      ∑ d ∈ f.support, dec (f d) = ∑ d ∈ f.support, Finsupp.single d (f d) := by
        apply Finset.sum_congr rfl
        intro d _
        exact hpiece (hf d)
      _ = f := Finsupp.sum_single f
  refine ⟨dec x, ⟨hmem x, hrd x⟩, ?_⟩
  intro f hf
  rw [← hf.2, hdr f hf.1]

theorem unique_homogeneous_decomposition (x : Presented n) :
    ∃! f : ℤ →₀ Presented n, (∀ d, f d ∈ degreePiece n d) ∧ f.sum (fun _ y => y)=x := by
  apply basis_homogeneous_decomposition (NilHeckeBasis.basis n) weight (degreePiece n) _ x
  intro d
  simpa only [NilHeckeBasis.basis_apply] using degreePiece_eq_leftPiece n d

theorem ONC.unique_homogeneous_decomposition (x : ONC.Q n) :
    ∃! f : ℤ →₀ ONC.Q n, (∀ d, f d ∈ ONC.degreePiece n d) ∧ f.sum (fun _ y => y)=x := by
  apply basis_homogeneous_decomposition (NilCoxeterPresentation.basis n) ONC.weight (ONC.degreePiece n) _ x
  intro d
  simpa only [NilCoxeterPresentation.basis_apply] using ONC.degreePiece_eq_basisPiece n d

/-- Exponent fiber appearing in the literal coefficient of the Laurent rational rank. -/
abbrev ExponentFiber (n : ℕ) (d : ℤ) (w : Perm n) :=
  {A : Fin (n+2) → ℕ // 2*(∑ j, A j : ℕ)-2*(length w : ℤ)=d}

instance exponentFiber_finite (n : ℕ) (d : ℤ) (w : Perm n) : Finite (ExponentFiber n d w) := by
  let embed : ExponentFiber n d w → (Fin (n+2) → Fin ((d+2*(length w : ℤ)).toNat+1)) :=
    fun A j => ⟨A.val j, by
      have h := A.property
      have hj : A.val j ≤ ∑ k, A.val k := Finset.single_le_sum (fun k _ => Nat.zero_le (A.val k)) (Finset.mem_univ j)
      have ht : (d+2*(length w : ℤ)).toNat ≥ ∑ k, A.val k := by omega
      omega⟩
  exact Finite.of_injective embed (fun A B h => Subtype.ext (funext (fun j =>
    congrArg Fin.val (congrFun h j))))

def degreeIndexEquiv (n : ℕ) (d : ℤ) : DegreeIndex n d ≃ Σ w : Perm n, ExponentFiber n d w where
  toFun i := ⟨i.val.2, ⟨i.val.1,i.property⟩⟩
  invFun i := ⟨(i.2.val,i.1),i.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance degreeIndex_finite (n : ℕ) (d : ℤ) : Finite (DegreeIndex n d) :=
  Finite.of_equiv _ (degreeIndexEquiv n d).symm
instance degree_free (n : ℕ) (d : ℤ) : Module.Free ℤ (degreePiece n d) :=
  Module.Free.of_basis (degreeLeftBasis n d)
instance degree_finite (n : ℕ) (d : ℤ) : Module.Finite ℤ (degreePiece n d) := by
  letI := Fintype.ofFinite (DegreeIndex n d)
  exact Module.Finite.of_basis (degreeLeftBasis n d)

/-- Coefficient identity at EVERY integer d, not merely a basis-cardinality statement. -/
theorem degree_finrank_coefficient (n : ℕ) (d : ℤ) :
    Module.finrank ℤ (degreePiece n d) = ∑ w : Perm n, Nat.card (ExponentFiber n d w) := by
  letI := Fintype.ofFinite (DegreeIndex n d)
  rw [Module.finrank_eq_card_basis (degreeLeftBasis n d), ← Nat.card_eq_fintype_card,
    Nat.card_congr (degreeIndexEquiv n d), Nat.card_sigma]

/-- Stars-and-bars on actual exponent vectors; signs do not enter this count. -/
theorem exponent_sum_card (n t : ℕ) :
    Nat.card {A : Fin (n+2) → ℕ // ∑ j, A j=t} = (t+n+1).choose (n+1) := by
  classical
  let S := Finset.piAntidiag (Finset.univ : Finset (Fin (n+2))) t
  have he : {A : Fin (n+2) → ℕ // ∑ j, A j=t} ≃ S :=
    Equiv.subtypeEquivRight (fun A => by simp [S, Finset.mem_piAntidiag])
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_coe]
  change (Finset.piAntidiag (Finset.univ : Finset (Fin (n+2))) t).card = _
  rw [← Finset.map_sym_eq_piAntidiag, Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hn : n+2+t-1=t+n+1 := by omega
  rw [hn, ← Nat.choose_symm (show t ≤ t+n+1 by omega)]
  congr 1
  omega

/-- Parity and nonnegative exponent condition are explicit, not implicit floor division. -/
def admissible (d : ℤ) (w : Perm n) : Prop :=
  0 ≤ d+2*(length w : ℤ) ∧ (d+2*(length w : ℤ)) % 2 = 0

instance (d : ℤ) (w : Perm n) : Decidable (admissible d w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem exponentFiber_card (n : ℕ) (d : ℤ) (w : Perm n) :
    Nat.card (ExponentFiber n d w) =
      if admissible d w then (((d+2*(length w : ℤ))/2).toNat+n+1).choose (n+1) else 0 := by
  classical
  by_cases h : admissible d w
  · rw [if_pos h]
    have he : ExponentFiber n d w ≃
        {A : Fin (n+2) → ℕ // ∑ j, A j=((d+2*(length w : ℤ))/2).toNat} :=
      Equiv.subtypeEquivRight (fun A => by
        rcases h with ⟨hpos,hmod⟩
        omega)
    rw [Nat.card_congr he, exponent_sum_card]
  · rw [if_neg h]
    have hempty : IsEmpty (ExponentFiber n d w) := ⟨fun A => by
      have ha := A.property
      apply h
      unfold admissible
      omega⟩
    exact Nat.card_eq_zero.mpr (Or.inl hempty)

theorem degree_finrank_binomial (n : ℕ) (d : ℤ) :
    Module.finrank ℤ (degreePiece n d) = ∑ w : Perm n,
      if admissible d w then (((d+2*(length w : ℤ))/2).toNat+n+1).choose (n+1) else 0 := by
  rw [degree_finrank_coefficient]
  apply Finset.sum_congr rfl
  intro w _
  exact exponentFiber_card n d w

/-- Ordinary inversion count, generalized in the auxiliary induction only. -/
def inversions {m : ℕ} (w : Equiv.Perm (Fin m)) : ℕ :=
  ∑ a : Fin m, ∑ b : Fin m, if a < b ∧ w b < w a then 1 else 0

/-- Insert the first image at p; remaining images retain their relative order. -/
def insertPerm {m : ℕ} (p : Fin (m+1)) (w : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0,w)
@[simp] theorem insertPerm_zero {m : ℕ} (p : Fin (m+1)) (w : Equiv.Perm (Fin m)) :
    insertPerm p w 0 = p := by simp [insertPerm, Equiv.Perm.mul_apply]
@[simp] theorem insertPerm_succ {m : ℕ} (p : Fin (m+1)) (w : Equiv.Perm (Fin m)) (i : Fin m) :
    insertPerm p w i.succ = p.succAbove (w i) := by
  simp [insertPerm, Equiv.Perm.mul_apply]

theorem insertPerm_bijective (m : ℕ) :
    Function.Bijective (fun pw : Fin (m+1) × Equiv.Perm (Fin m) => insertPerm pw.1 pw.2) := by
  constructor
  · rintro ⟨p,w⟩ ⟨q,v⟩ h
    have hp : p=q := by simpa using congrArg (fun e : Equiv.Perm (Fin (m+1)) => e 0) h
    subst q
    have hw : w=v := by
      apply Equiv.ext
      intro i
      have hi := congrArg (fun e : Equiv.Perm (Fin (m+1)) => e i.succ) h
      apply Fin.succAbove_right_injective (p:=p)
      simpa only [insertPerm_succ] using hi
    subst v
    rfl
  · intro σ
    let τ : Equiv.Perm (Fin (m+1)) := (σ 0).cycleRange * σ
    have hzero : τ 0=0 := by simp [τ, Equiv.Perm.mul_apply]
    obtain ⟨pw,hpw⟩ := Equiv.Perm.decomposeFin.symm.surjective τ
    obtain ⟨q,w⟩ := pw
    have hq : q=0 := by
      have h := congrArg (fun e : Equiv.Perm (Fin (m+1)) => e 0) hpw
      simpa only [Equiv.Perm.decomposeFin_symm_apply_zero, hzero] using h
    subst q
    refine ⟨(σ 0,w), ?_⟩
    change (σ 0).cycleRange.symm * Equiv.Perm.decomposeFin.symm (0,w) = σ
    rw [hpw]
    change (σ 0).cycleRange⁻¹ * ((σ 0).cycleRange * σ) = σ
    simp only [← mul_assoc, inv_mul_cancel, one_mul]

def insertionEquiv (m : ℕ) : (Fin (m+1) × Equiv.Perm (Fin m)) ≃ Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective _ (insertPerm_bijective m)

theorem count_below (m r : ℕ) (hr : r ≤ m) :
    (∑ i : Fin m, if i.val < r then 1 else 0 : ℕ)=r := by
  induction m with
  | zero =>
    have h : r=0 := by omega
    simp [h]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases h : r ≤ m
    · simp only [Fin.coe_castSucc, Fin.val_last, if_neg (by omega : ¬m<r), add_zero]
      exact ih h
    · have he : r=m+1 := by omega
      subst r
      simp only [Fin.coe_castSucc, Fin.val_last, Nat.lt_succ_self, if_true]
      have hall : (∑ i : Fin m, if i.val < m+1 then 1 else 0 : ℕ)=m := by
        simp only [show ∀ i : Fin m, i.val < m+1 from fun i => by omega, if_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      rw [hall]

theorem inversions_insert {m : ℕ} (p : Fin (m+1)) (w : Equiv.Perm (Fin m)) :
    inversions (insertPerm p w)=p.val+inversions w := by
  unfold inversions
  rw [Fin.sum_univ_succ]
  have hfirst : (∑ b : Fin (m+1), if (0 : Fin (m+1)) < b ∧ insertPerm p w b < insertPerm p w 0
      then 1 else 0 : ℕ)=p.val := by
    rw [Fin.sum_univ_succ]
    simp only [lt_self_iff_false, false_and, if_false, Fin.succ_pos, true_and,
      insertPerm_succ, insertPerm_zero, Fin.succAbove_lt_iff_castSucc_lt, zero_add]
    change (∑ b : Fin m, if (w b).val < p.val then 1 else 0 : ℕ)=p.val
    rw [Equiv.sum_comp w (fun i => if i.val < p.val then (1 : ℕ) else 0)]
    exact count_below m p.val (by omega)
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.sum_univ_succ]
  simp only [Fin.not_lt_zero, false_and, if_false, zero_add, Fin.succ_lt_succ_iff,
    insertPerm_succ, (Fin.strictMono_succAbove p).lt_iff_lt]

/-- Inversion generating polynomial; specialize R=ℤ[t] for a literal polynomial identity. -/
theorem inversion_generating {R : Type*} [CommSemiring R] (t : R) (m : ℕ) :
    ∑ w : Equiv.Perm (Fin m), t ^ inversions w =
      ∏ j ∈ Finset.range m, ∑ k ∈ Finset.range (j+1), t^k := by
  classical
  induction m with
  | zero => simp [inversions]
  | succ m ih =>
    calc
      ∑ w : Equiv.Perm (Fin (m+1)), t ^ inversions w =
          ∑ pw : Fin (m+1) × Equiv.Perm (Fin m), t ^ inversions (insertPerm pw.1 pw.2) :=
        ((insertionEquiv m).sum_comp (fun w => t ^ inversions w)).symm
      _ = (∑ p : Fin (m+1), t^p.val) * (∑ w : Equiv.Perm (Fin m), t^inversions w) := by
        simp only [Fintype.sum_prod_type, inversions_insert, pow_add, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = _ := by
        rw [ih, Fin.sum_univ_eq_sum_range, Finset.prod_range_succ]
        exact mul_comm _ _

theorem ONC.inversion_generating_polynomial (n : ℕ) :
    (∑ w : Perm n, (Polynomial.X : Polynomial ℤ) ^ length w) =
      ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), (Polynomial.X : Polynomial ℤ)^k :=
  inversion_generating Polynomial.X (n+2)

/-- Substitution t=q⁻² supplies exactly the negative-degree numerator in (2.44). -/
theorem ONC.q_rank_numerator {K : Type*} [Field K] (q : K) (n : ℕ) :
    (∑ w : Perm n, (q⁻¹)^(2*length w)) =
      ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), (q⁻¹)^(2*k) := by
  simpa only [pow_mul] using inversion_generating ((q⁻¹)^2) (n+2)

/-- No odd integer degree exists: paper parity follows from the actual word grading. -/
theorem degreePiece_odd (n : ℕ) (d : ℤ) (hd : d % 2 ≠ 0) : degreePiece n d = ⊥ := by
  rw [degreePiece_eq_leftPiece]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have h := i.property
  unfold weight at h
  exfalso
  omega

theorem ONC.degreePiece_odd (n : ℕ) (d : ℤ) (hd : d % 2 ≠ 0) : ONC.degreePiece n d = ⊥ := by
  rw [ONC.degreePiece_eq_basisPiece]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have h := i.property
  unfold ONC.weight at h
  exfalso
  omega

theorem ONC.degreePiece_positive (n : ℕ) (d : ℤ) (hd : 0 < d) : ONC.degreePiece n d = ⊥ := by
  rw [ONC.degreePiece_eq_basisPiece]
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have h := i.property
  unfold ONC.weight at h
  exfalso
  omega

/-- The paper symmetric q-integer convention, including its triangular shift.
The factors at j are [j+1]=q^j+q^(j-2)+...+q^(-j); no Laurent-series carrier is assumed. -/
theorem ONC.q_rank_shifted_factorial {K : Type*} [Field K] (q : K) (hq : q ≠ 0) (n : ℕ) :
    (∑ w : Perm n, (q⁻¹)^(2*length w)) =
      q ^ (-(((n+2)*(n+1)/2 : ℕ) : ℤ)) *
      ∏ j ∈ Finset.range (n+2), ∑ k ∈ Finset.range (j+1), q^((j : ℤ)-2*(k : ℤ)) := by
  have factor (j : ℕ) : (∑ k ∈ Finset.range (j+1), (q⁻¹)^(2*k)) =
      q^(-(j : ℤ)) * ∑ k ∈ Finset.range (j+1), q^((j : ℤ)-2*(k : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← zpow_add₀ hq]
    have he : -(j : ℤ)+((j : ℤ)-2*(k : ℤ)) = -((2*k : ℕ) : ℤ) := by push_cast; ring
    rw [he, zpow_neg, zpow_natCast, inv_pow]
  have hp (s : Finset ℕ) : (∏ j ∈ s, q^(-(j : ℤ))) = q^(-((∑ j ∈ s, j : ℕ) : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih]
      push_cast
      rw [neg_add, zpow_add₀ hq]
  rw [ONC.q_rank_numerator]
  simp_rw [factor]
  rw [Finset.prod_mul_distrib, hp, Finset.sum_range_id]
  congr 2

end
end OddMath.Frontier.NilHeckeGrading
