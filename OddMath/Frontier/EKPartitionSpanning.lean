import OddMath.Frontier.EKQuotientRelations
import OddMath.Frontier.DegreeShapes

/-! EK 1107.5610v2 p15, Corollary 2.12: integral SPANNING only.
The adjacent odd relation is tautological when used inward at gap one.
We instead solve the relation one step OUTWARD, then induct on the smaller
index. Word termination is the natural weighted-position measure. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKPartitionSpanning
open EKRadicalQuotient

def hPartition (μ : YoungDiagram) : Q := (μ.rowLens.map EKElementaryQuotient.h).prod
def ePartition (μ : YoungDiagram) : Q := (μ.rowLens.map EKElementaryQuotient.e).prod

def g (c : Bool) (a : ℕ) : Q := pi (EKMixedPairing.gen c a)
def word (c : Bool) (w : List ℕ) : Q := (w.map (g c)).prod

@[simp] theorem g_zero (c : Bool) : g c 0 = 1 := by simp [g]
@[simp] theorem word_nil (c : Bool) : word c [] = 1 := rfl
@[simp] theorem word_cons (c : Bool) (a : ℕ) (w : List ℕ) :
    word c (a::w) = g c a * word c w := rfl
@[simp] theorem word_append (c : Bool) (u v : List ℕ) :
    word c (u++v) = word c u * word c v := by simp [word]

/-- Integral two-letter straightening in any context. Every output pair has
unchanged weight and first index at least the original larger index.
The zero/unit case terminates the OUTWARD recurrence, with no division by 2. -/
theorem pair_mem (c : Bool) (S : Submodule ℤ Q) (L R : Q) (a b : ℕ)
    (hab : a ≤ b)
    (hh : ∀ u v : ℕ, u+v=a+b → b ≤ u → L*(g c u*g c v)*R ∈ S) :
    L*(g c a*g c b)*R ∈ S := by
  induction a generalizing b with
  | zero =>
    simpa using hh b 0 (by omega) (by omega)
  | succ a ih =>
    by_cases he : Even (a+1+b)
    · rw [show g c (a+1)*g c b = g c b*g c (a+1) from
        EKQuotientRelations.same_even c (a+1) b he]
      exact hh b (a+1) (by omega) le_rfl
    · have hp : Even (a+b) := by
        rw [Nat.even_iff] at *
        omega
      have hX : L*(g c a*g c (b+1))*R ∈ S :=
        ih (b+1) (by omega) (fun u v huv hu => hh u v (by omega) (by omega))
      have hY := hh (b+1) a (by omega) (by omega)
      have hZ := hh b (a+1) (by omega) le_rfl
      have hr := congrArg (fun x : Q => L*x*R)
        (EKQuotientRelations.same_odd_succ c a b hp)
      change L*(g c a*g c (b+1) + (-1 : ℤ)^a • (g c (b+1)*g c a))*R =
        L*((-1 : ℤ)^a • (g c (a+1)*g c b) + g c b*g c (a+1))*R at hr
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] at hr
      have hm := S.sub_mem (S.add_mem hX (S.smul_mem ((-1 : ℤ)^a) hY)) hZ
      rw [hr, add_sub_cancel_right] at hm
      rcases neg_one_pow_eq_or ℤ a with hs | hs
      · simpa [hs] using hm
      · simpa [hs] using S.neg_mem hm

/-- Position-weight, zero at the first position. -/
def cost : List ℕ → ℕ
  | [] => 0
  | _::w => w.sum + cost w

theorem cost_append (p w : List ℕ) :
    cost (p++w) = cost p + p.length*w.sum + cost w := by
  induction p with
  | nil => simp [cost]
  | cons a p ih => simp [cost, ih, Nat.add_mul]; omega

/-- Each straightened adjacent pair strictly lowers the global measure. -/
theorem cost_replace (p q : List ℕ) {a b u v : ℕ}
    (hab : a < b) (huv : u+v=a+b) (hu : b ≤ u) :
    cost (p++u::v::q) < cost (p++a::b::q) := by
  have hv : v < b := by omega
  simp only [cost_append, cost, List.sum_cons]
  have he : u+(v+q.sum)=a+(b+q.sum) := by omega
  rw [he]
  omega

/-- A nonsorted word contains an adjacent strict ascent. -/
theorem sorted_or_ascent (w : List ℕ) :
    w.Sorted (· ≥ ·) ∨ ∃ p q a b, w=p++a::b::q ∧ a<b := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons a w ih =>
    rcases ih with hs | ⟨p,q,b,d,hw,hbd⟩
    · cases w with
      | nil => exact Or.inl (by simp)
      | cons b q =>
        by_cases hba : b ≤ a
        · exact Or.inl (List.Sorted.cons hba hs)
        · exact Or.inr ⟨[],q,a,b,rfl,by omega⟩
    · exact Or.inr ⟨a::p,q,b,d,by simp [hw],hbd⟩

/-- All words of a given weight lie in any submodule containing the sorted
words of that weight. The induction is over an actual natural measure. -/
theorem word_mem_of_sorted (c : Bool) (S : Submodule ℤ Q) (d : ℕ)
    (hs : ∀ w : List ℕ, w.Sorted (· ≥ ·) → w.sum=d → word c w ∈ S)
    (w : List ℕ) (hd : w.sum=d) : word c w ∈ S := by
  induction h : cost w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rcases sorted_or_ascent w with hw | ⟨p,q,a,b,rfl,hab⟩
    · exact hs w hw hd
    · simp only [word_append, word_cons]
      have hh := pair_mem c S (word c p) (word c q) a b (by omega)
        (fun u v huv hu => by
          have hc := cost_replace p q hab huv hu
          have hh : (p++u::v::q).sum=d := by
            simp only [List.sum_append, List.sum_cons] at hd ⊢
            omega
          have hm := ih (cost (p++u::v::q)) (by omega) (p++u::v::q) hh rfl
          simpa only [word_append, word_cons, mul_assoc] using hm)
      simpa only [mul_assoc] using hh

/-- The literal cells construction counts every part, including zero parts. -/
theorem card_cellsOfRowLens (w : List ℕ) :
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simp [ih]
    · apply Finset.disjoint_left.mpr
      rintro ⟨i,j⟩ hp hq
      simp only [Finset.mem_product, Finset.mem_singleton] at hp
      obtain ⟨rfl, _⟩ := hp
      rcases Finset.mem_map.mp hq with ⟨⟨u,v⟩, _, hh⟩
      have he := congrArg Prod.fst hh
      simp at he

theorem card_ofRowLens (w : List ℕ) (hw : w.Sorted (· ≥ ·)) :
    (YoungDiagram.ofRowLens w hw).card = w.sum := card_cellsOfRowLens w

/-- Removing zero generators preserves both the product and its exact weight. -/
theorem erase_zeros (c : Bool) (w : List ℕ) :
    word c (w.filter (fun a => a != 0)) = word c w ∧
    (w.filter (fun a => a != 0)).sum = w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases ha : a=0
    · subst a; simpa using ih
    · simp [ha, ih.1, ih.2]

/-- Sorted words, with arbitrary zero padding, are literal partition words. -/
theorem sorted_is_partition (c : Bool) (w : List ℕ) (hw : w.Sorted (· ≥ ·)) :
    ∃ μ : YoungDiagram, μ.card=w.sum ∧ word c μ.rowLens=word c w := by
  let v := w.filter (fun a => a != 0)
  have hv : v.Sorted (· ≥ ·) := hw.filter _
  have hp : ∀ a ∈ v, 0<a := by
    intro a ha
    simp only [v, List.mem_filter, bne_iff_ne, ne_eq] at ha
    omega
  refine ⟨YoungDiagram.ofRowLens v hv, ?_, ?_⟩
  · rw [card_ofRowLens]
    exact (erase_zeros c w).2
  · rw [YoungDiagram.rowLens_ofRowLens_eq_self hp]
    exact (erase_zeros c w).1

/-- Degree-indexed spanning in the exact exhaustive YoungDiagram family. -/
theorem word_mem_degree_span (c : Bool) (w : List ℕ) :
    word c w ∈ Submodule.span ℤ
      (Set.range (fun μ : DegreeShapes.DegreeShape w.sum => word c μ.val.rowLens)) := by
  apply word_mem_of_sorted c _ w.sum _ w rfl
  intro v hv hd
  obtain ⟨μ, hμ, he⟩ := sorted_is_partition c v hv
  rw [← he]
  exact Submodule.subset_span ⟨⟨μ, hμ.trans hd⟩, rfl⟩

/-- A finite integral expansion preserving the total weight, for either color. -/
theorem word_expansion (c : Bool) (w : List ℕ) :
    letI := DegreeShapes.degreeFintype w.sum
    ∃ a : DegreeShapes.DegreeShape w.sum → ℤ,
      word c w = ∑ μ, a μ • word c μ.val.rowLens := by
  classical
  letI := DegreeShapes.degreeFintype w.sum
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (word_mem_degree_span c w)
  exact ⟨a, ha.symm⟩

/-- EK Cor 2.12 spanning, complete words, including the empty word and h₀. -/
theorem h_word_expansion (w : List ℕ) :
    letI := DegreeShapes.degreeFintype w.sum
    ∃ a : DegreeShapes.DegreeShape w.sum → ℤ,
      (w.map EKElementaryQuotient.h).prod = ∑ μ, a μ • hPartition μ.val :=
  word_expansion false w

/-- EK Cor 2.12 spanning, elementary words, including the empty word and e₀. -/
theorem e_word_expansion (w : List ℕ) :
    letI := DegreeShapes.degreeFintype w.sum
    ∃ a : DegreeShapes.DegreeShape w.sum → ℤ,
      (w.map EKElementaryQuotient.e).prod = ∑ μ, a μ • ePartition μ.val :=
  word_expansion true w

/-- Forgetting the degree index gives the global partition span. -/
theorem word_mem_partition_span (c : Bool) (w : List ℕ) :
    word c w ∈ Submodule.span ℤ (Set.range (fun μ : YoungDiagram => word c μ.rowLens)) := by
  apply (Submodule.span_mono ?_) (word_mem_degree_span c w)
  rintro _ ⟨μ, rfl⟩
  exact ⟨μ.val, rfl⟩

private def colorEquiv (c : Bool) : CompleteElementary.A ≃ₐ[ℤ] CompleteElementary.A :=
  if c then CompleteChangeOfGenerators.completeElementaryEquiv else AlgEquiv.refl

private theorem colorEquiv_h (c : Bool) (n : ℕ) :
    colorEquiv c (CompleteElementary.h n) = EKMixedPairing.gen c n := by
  cases c
  · rfl
  · exact CompleteChangeOfGenerators.completeToElementary_h n

private theorem image_wordBasis (c : Bool) (w : EKFreeCoproduct.W) :
    pi (colorEquiv c (EKFreeCoproduct.wordBasis w)) =
      word c (List.ofFn (EKPairingAdjoint.parts w)) := by
  rw [← EKPairingAdjoint.vWord_parts w]
  simp only [EKPairingAdjoint.vWord, CompleteElementary.hWord, map_list_prod,
    List.map_map, Function.comp_def, colorEquiv_h]
  rfl

/-- Actual quotient generation for BOTH colors. Elementary generation uses the
proved free-algebra change of variables, not a quotient automorphism assumption. -/
theorem partition_span (c : Bool) :
    Submodule.span ℤ (Set.range (fun μ : YoungDiagram => word c μ.rowLens)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨x, rfl⟩ := pi_surjective x
  obtain ⟨x, rfl⟩ := (colorEquiv c).surjective x
  induction x using EKPairingAdjoint.basis_induction EKFreeCoproduct.wordBasis with
  | hz => simp
  | ha a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | hb w r =>
    simp only [map_smul, map_zsmul, image_wordBasis]
    exact Submodule.smul_mem _ r (word_mem_partition_span c _)

/-- Global complete-partition spanning of the actual radical quotient over ℤ. -/
theorem h_span : Submodule.span ℤ (Set.range hPartition) = ⊤ := partition_span false

/-- Global elementary-partition spanning of the actual radical quotient over ℤ. -/
theorem e_span : Submodule.span ℤ (Set.range ePartition) = ⊤ := partition_span true

/-- Every actual quotient element is a finite integral sum of complete partitions. -/
theorem h_expansion (x : Q) :
    ∃ a : YoungDiagram →₀ ℤ, x = a.sum (fun μ z => z • hPartition μ) := by
  have hx : x ∈ Submodule.span ℤ (Set.range hPartition) := by rw [h_span]; trivial
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  exact ⟨a, ha.symm⟩

/-- Every actual quotient element is a finite integral sum of elementary partitions. -/
theorem e_expansion (x : Q) :
    ∃ a : YoungDiagram →₀ ℤ, x = a.sum (fun μ z => z • ePartition μ) := by
  have hx : x ∈ Submodule.span ℤ (Set.range ePartition) := by rw [e_span]; trivial
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  exact ⟨a, ha.symm⟩

end OddMath.Frontier.EKPartitionSpanning
