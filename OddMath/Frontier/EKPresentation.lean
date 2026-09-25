import OddMath.Frontier.EKIntegralBases
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! EK1107.5610v2 p15 Cor2.13, integer specialization.
The defining ideal is the two-sided span of precisely (2.11),(2.12).
Straightening is proved in this quotient BEFORE its map to Q is injective.
Every helper below discharges this presentation or h-to-e automorphism consumer. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace OddMath.Frontier.EKPresentation
open CompleteElementary (A)
open EKRadicalQuotient (Q pi)

/-- Literal complete relators; h0=1 is built into the free algebra. -/
inductive Relator : A → Prop
  | even (a b : ℕ) (hab : Even (a+b)) :
      Relator (CompleteElementary.h a * CompleteElementary.h b -
        CompleteElementary.h b * CompleteElementary.h a)
  | odd (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
      Relator (CompleteElementary.h a * CompleteElementary.h b +
        (-1 : ℤ)^a • (CompleteElementary.h b * CompleteElementary.h a) -
        ((-1 : ℤ)^a • (CompleteElementary.h (a+1) * CompleteElementary.h (b-1)) +
          CompleteElementary.h (b-1) * CompleteElementary.h (a+1)))

def relSet : Set A := {r | Relator r}
def relTwoSided : TwoSidedIdeal A := TwoSidedIdeal.span relSet
def relIdeal : Ideal A := relTwoSided.asIdeal
instance relIdealTwoSided : relIdeal.IsTwoSided :=
  inferInstanceAs (relTwoSided.asIdeal.IsTwoSided)
abbrev Presented := A ⧸ relIdeal

def mk : A →+* Presented := Ideal.Quotient.mk relIdeal
def h (n : ℕ) : Presented := mk (CompleteElementary.h n)
@[simp] theorem h_zero : h 0 = 1 := by simp [h]

private theorem relator_zero {r : A} (hr : Relator r) : mk r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ relTwoSided.asIdeal
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span hr

theorem complete_even (a b : ℕ) (hab : Even (a+b)) : h a*h b = h b*h a := by
  simpa only [map_sub, map_mul, h, sub_eq_zero] using relator_zero (Relator.even a b hab)

theorem complete_odd (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    h a*h b + (-1 : ℤ)^a • (h b*h a) =
      (-1 : ℤ)^a • (h (a+1)*h (b-1)) + h (b-1)*h (a+1) := by
  simpa only [map_sub, map_add, map_mul, map_zsmul, h, sub_eq_zero] using
    relator_zero (Relator.odd a b hb hab)

theorem complete_odd_succ (a b : ℕ) (hab : Even (a+b)) :
    h a*h (b+1) + (-1 : ℤ)^a • (h (b+1)*h a) =
      (-1 : ℤ)^a • (h (a+1)*h b) + h b*h (a+1) := by
  exact complete_odd a (b+1) (by omega) (by
    rw [Nat.odd_iff]; have := Nat.even_iff.mp hab; omega)

/-- Source generator substitution before imposing the relators. -/
def colorFree (c : Bool) : A ≃ₐ[ℤ] A :=
  if c then CompleteChangeOfGenerators.completeElementaryEquiv else AlgEquiv.refl

@[simp] theorem colorFree_h (c : Bool) (n : ℕ) :
    colorFree c (CompleteElementary.h n) = EKMixedPairing.gen c n := by
  cases c
  · rfl
  · exact CompleteChangeOfGenerators.completeToElementary_h n

def freeToColor (c : Bool) : A →+* Q := pi.comp (colorFree c).toRingHom
@[simp] theorem freeToColor_h (c : Bool) (n : ℕ) :
    freeToColor c (CompleteElementary.h n) = EKPartitionSpanning.g c n := by
  simp [freeToColor, EKPartitionSpanning.g]

theorem relation_killed (c : Bool) (r : A) (hr : r ∈ relSet) : freeToColor c r = 0 := by
  cases hr with
  | even a b hab =>
    simpa only [map_sub, map_mul, freeToColor_h, sub_eq_zero, EKPartitionSpanning.g] using
      EKQuotientRelations.same_even c a b hab
  | odd a b hb hab =>
    cases b with
    | zero => omega
    | succ b =>
      have he : Even (a+b) := by
        rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
      simpa only [map_sub, map_add, map_mul, map_zsmul, freeToColor_h,
        Nat.add_sub_cancel, sub_eq_zero, EKPartitionSpanning.g] using
        EKQuotientRelations.same_odd_succ c a b he

theorem ideal_killed (c : Bool) (r : A) (hr : r ∈ relIdeal) : freeToColor c r = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x hx => exact relation_killed c x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

def toColor (c : Bool) : Presented →+* Q :=
  Ideal.Quotient.lift relIdeal (freeToColor c) (ideal_killed c)
@[simp] theorem toColor_mk (c : Bool) (x : A) : toColor c (mk x) = freeToColor c x := rfl
@[simp] theorem toColor_h (c : Bool) (n : ℕ) :
    toColor c (h n) = EKPartitionSpanning.g c n := freeToColor_h c n

/-- Canonical map by actual complete generators, NOT used to pull back relations. -/
def toQ : Presented →+* Q := toColor false
@[simp] theorem toQ_mk (x : A) : toQ (mk x) = pi x := rfl
@[simp] theorem toQ_h (n : ℕ) : toQ (h n) = EKElementaryQuotient.h n := toColor_h false n

def word (w : List ℕ) : Presented := (w.map h).prod
@[simp] theorem word_nil : word [] = 1 := rfl
@[simp] theorem word_cons (a : ℕ) (w : List ℕ) : word (a::w) = h a * word w := rfl
@[simp] theorem word_append (u v : List ℕ) : word (u++v) = word u * word v := by simp [word]

/-- Integral two-letter straightening in any context. Every output pair has
unchanged weight and first index at least the original larger index.
The zero/unit case terminates the OUTWARD recurrence, with no division by 2. -/
theorem pair_mem (S : Submodule ℤ Presented) (L R : Presented) (a b : ℕ)
    (hab : a ≤ b)
    (hh : ∀ u v : ℕ, u+v=a+b → b ≤ u → L*(h u*h v)*R ∈ S) :
    L*(h a*h b)*R ∈ S := by
  induction a generalizing b with
  | zero =>
    simpa using hh b 0 (by omega) (by omega)
  | succ a ih =>
    by_cases he : Even (a+1+b)
    · rw [show h (a+1)*h b = h b*h (a+1) from
        complete_even (a+1) b he]
      exact hh b (a+1) (by omega) le_rfl
    · have hp : Even (a+b) := by
        rw [Nat.even_iff] at *
        omega
      have hX : L*(h a*h (b+1))*R ∈ S :=
        ih (b+1) (by omega) (fun u v huv hu => hh u v (by omega) (by omega))
      have hY := hh (b+1) a (by omega) (by omega)
      have hZ := hh b (a+1) (by omega) le_rfl
      have hr := congrArg (fun x : Presented => L*x*R)
        (complete_odd_succ a b hp)
      change L*(h a*h (b+1) + (-1 : ℤ)^a • (h (b+1)*h a))*R =
        L*((-1 : ℤ)^a • (h (a+1)*h b) + h b*h (a+1))*R at hr
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] at hr
      have hm := S.sub_mem (S.add_mem hX (S.smul_mem ((-1 : ℤ)^a) hY)) hZ
      rw [hr, add_sub_cancel_right] at hm
      rcases neg_one_pow_eq_or ℤ a with hs | hs
      · simpa [hs] using hm
      · simpa [hs] using S.neg_mem hm


open EKPartitionSpanning (cost cost_replace sorted_or_ascent card_ofRowLens)

/-- All words of a given weight lie in any submodule containing the sorted
words of that weight. The induction is over an actual natural measure. -/
theorem word_mem_of_sorted (S : Submodule ℤ Presented) (d : ℕ)
    (hs : ∀ w : List ℕ, w.Sorted (· ≥ ·) → w.sum=d → word w ∈ S)
    (w : List ℕ) (hd : w.sum=d) : word w ∈ S := by
  induction h : cost w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rcases sorted_or_ascent w with hw | ⟨p,q,a,b,rfl,hab⟩
    · exact hs w hw hd
    · simp only [word_append, word_cons]
      have hh := pair_mem S (word p) (word q) a b (by omega)
        (fun u v huv hu => by
          have hc := cost_replace p q hab huv hu
          have hh : (p++u::v::q).sum=d := by
            simp only [List.sum_append, List.sum_cons] at hd ⊢
            omega
          have hm := ih (cost (p++u::v::q)) (by omega) (p++u::v::q) hh rfl
          simpa only [word_append, word_cons, mul_assoc] using hm)
      simpa only [mul_assoc] using hh

/-- Removing zero generators preserves both the product and its exact weight. -/
theorem erase_zeros (w : List ℕ) :
    word (w.filter (fun a => a != 0)) = word w ∧
    (w.filter (fun a => a != 0)).sum = w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases ha : a=0
    · subst a; simpa using ih
    · simp [ha, ih.1, ih.2]

/-- Sorted words, with arbitrary zero padding, are literal partition words. -/
theorem sorted_is_partition (w : List ℕ) (hw : w.Sorted (· ≥ ·)) :
    ∃ μ : YoungDiagram, μ.card=w.sum ∧ word μ.rowLens=word w := by
  let v := w.filter (fun a => a != 0)
  have hv : v.Sorted (· ≥ ·) := hw.filter _
  have hp : ∀ a ∈ v, 0<a := by
    intro a ha
    simp only [v, List.mem_filter, bne_iff_ne, ne_eq] at ha
    omega
  refine ⟨YoungDiagram.ofRowLens v hv, ?_, ?_⟩
  · rw [card_ofRowLens]
    exact (erase_zeros w).2
  · rw [YoungDiagram.rowLens_ofRowLens_eq_self hp]
    exact (erase_zeros w).1

/-- Degree-indexed spanning in the exact exhaustive YoungDiagram family. -/
theorem word_mem_degree_span (w : List ℕ) :
    word w ∈ Submodule.span ℤ
      (Set.range (fun μ : DegreeShapes.DegreeShape w.sum => word μ.val.rowLens)) := by
  apply word_mem_of_sorted _ w.sum _ w rfl
  intro v hv hd
  obtain ⟨μ, hμ, he⟩ := sorted_is_partition v hv
  rw [← he]
  exact Submodule.subset_span ⟨⟨μ, hμ.trans hd⟩, rfl⟩


/-- Global Presented-side partition span; its proof uses no injectivity claim. -/
def partition (μ : YoungDiagram) : Presented := word μ.rowLens

theorem word_mem_partition_span (w : List ℕ) :
    word w ∈ Submodule.span ℤ (Set.range partition) := by
  apply (Submodule.span_mono ?_) (word_mem_degree_span w)
  rintro _ ⟨μ, rfl⟩
  exact ⟨μ.val, rfl⟩

@[simp] theorem mk_wordBasis (w : EKFreeCoproduct.W) :
    mk (EKFreeCoproduct.wordBasis w) = word (List.ofFn (EKPairingAdjoint.parts w)) := by
  rw [← EKPairingAdjoint.vWord_parts w]
  simp only [EKPairingAdjoint.vWord, CompleteElementary.hWord, map_list_prod,
    List.map_map, Function.comp_def, word, h]
  rfl

theorem partition_span : Submodule.span ℤ (Set.range partition) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨x, rfl⟩ := (Ideal.Quotient.mk_surjective : Function.Surjective mk) x
  induction x using EKPairingAdjoint.basis_induction EKFreeCoproduct.wordBasis with
  | hz => simp
  | ha a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | hb w r =>
    change mk (r • EKFreeCoproduct.wordBasis w) ∈ _
    rw [map_zsmul, mk_wordBasis]
    exact Submodule.smul_mem _ r (word_mem_partition_span _)

theorem exists_expansion (x : Presented) :
    ∃ a : YoungDiagram →₀ ℤ, a.sum (fun μ z => z • partition μ) = x := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  rw [partition_span]
  trivial

@[simp] theorem toColor_word (c : Bool) (w : List ℕ) :
    toColor c (word w) = EKPartitionSpanning.word c w := by
  simp only [word, map_list_prod, List.map_map, Function.comp_def,
    toColor_h, EKPartitionSpanning.word]

@[simp] theorem toColor_partition (c : Bool) (μ : YoungDiagram) :
    toColor c (partition μ) = EKPartitionSpanning.word c μ.rowLens := toColor_word c _

theorem image_linearIndependent (c : Bool) :
    LinearIndependent ℤ (fun μ : YoungDiagram => toColor c (partition μ)) := by
  cases c
  · simpa only [toColor_partition] using EKSemiorthogonality.hPartition_linearIndependent
  · simpa only [toColor_partition] using EKSemiorthogonality.ePartition_linearIndependent

/-- No rank argument: every presented element has a literal partition expansion,
and its image has unique integral coordinates in Q. -/
theorem toColor_injective (c : Bool) : Function.Injective (toColor c) := by
  intro x y heq
  obtain ⟨a, ha⟩ := exists_expansion x
  obtain ⟨b, hb⟩ := exists_expansion y
  have he : a.sum (fun μ z => z • toColor c (partition μ)) =
      b.sum (fun μ z => z • toColor c (partition μ)) := by
    have hh := (congrArg (toColor c) ha).trans (heq.trans (congrArg (toColor c) hb).symm)
    simpa only [Finsupp.sum, map_sum, map_zsmul] using hh
  have hab := (image_linearIndependent c).finsuppLinearCombination_injective he
  subst b
  exact ha.symm.trans hb

/-- Onto by the already-proved free-algebra change of variables, not equal rank. -/
theorem toColor_surjective (c : Bool) : Function.Surjective (toColor c) := by
  intro x
  obtain ⟨y, rfl⟩ := EKRadicalQuotient.pi_surjective x
  obtain ⟨z, rfl⟩ := (colorFree c).surjective y
  exact ⟨mk z, rfl⟩

theorem toQ_bijective : Function.Bijective toQ :=
  ⟨toColor_injective false, toColor_surjective false⟩

/-- EK Cor2.13 generators-and-relations statement on the actual two quotients. -/
def presentationEquiv : Presented ≃+* Q := RingEquiv.ofBijective toQ toQ_bijective
@[simp] theorem presentationEquiv_apply (x : Presented) : presentationEquiv x = toQ x := rfl
@[simp] theorem presentationEquiv_h (n : ℕ) :
    presentationEquiv (h n) = EKElementaryQuotient.h n := toQ_h n

def elementaryPresentationEquiv : Presented ≃+* Q :=
  RingEquiv.ofBijective (toColor true) ⟨toColor_injective true, toColor_surjective true⟩
@[simp] theorem elementaryPresentationEquiv_apply (x : Presented) :
    elementaryPresentationEquiv x = toColor true x := rfl

/-- Actual multiplicative automorphism, with both inverse laws supplied by the
proved bijections. This is NOT declared to be an involution. -/
def psi1 : Q ≃+* Q := presentationEquiv.symm.trans elementaryPresentationEquiv

@[simp] theorem psi1_toQ (x : Presented) : psi1 (toQ x) = toColor true x := by
  change elementaryPresentationEquiv (presentationEquiv.symm (presentationEquiv x)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

@[simp] theorem psi1_h (n : ℕ) : psi1 (EKElementaryQuotient.h n) = EKElementaryQuotient.e n := by
  rw [← toQ_h, psi1_toQ, toColor_h]
  rfl

/-- Arbitrary free element, not merely a finite test of generators. -/
theorem psi1_pi (x : A) :
    psi1 (pi x) = pi (CompleteChangeOfGenerators.completeToElementary x) := by
  rw [← toQ_mk, psi1_toQ, toColor_mk]
  rfl

/-- The genuine inverse is the recursive recovered-complete substitution. -/
theorem psi1_symm_pi (x : A) :
    psi1.symm (pi x) = pi (CompleteChangeOfGenerators.elementaryToComplete x) := by
  apply psi1.injective
  rw [RingEquiv.apply_symm_apply, psi1_pi]
  have hh := congrArg (fun f : A →ₐ[ℤ] A => f x)
    CompleteChangeOfGenerators.completeToElementary_comp_elementaryToComplete
  exact congrArg pi hh.symm

theorem psi1_symm_h (n : ℕ) :
    psi1.symm (EKElementaryQuotient.h n) =
      pi (CompleteChangeOfGenerators.recoveredComplete n) := by
  rw [EKElementaryQuotient.h, psi1_symm_pi,
    CompleteChangeOfGenerators.elementaryToComplete_h]

theorem psi1_word (w : List ℕ) :
    psi1 ((w.map EKElementaryQuotient.h).prod) = (w.map EKElementaryQuotient.e).prod := by
  simp only [map_list_prod, List.map_map, Function.comp_def, psi1_h]

theorem psi1_inverse_word (w : List ℕ) :
    psi1.symm ((w.map EKElementaryQuotient.e).prod) = (w.map EKElementaryQuotient.h).prod := by
  rw [← psi1_word, RingEquiv.symm_apply_apply]

end OddMath.Frontier.EKPresentation
