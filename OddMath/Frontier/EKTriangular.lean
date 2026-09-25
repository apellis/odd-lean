import OddMath.Frontier.EKAutomorphisms

/-! EK Lemma 2.16: lexicographic straightening of the literal h-basis.
All spans and coordinates are over ℤ in the inherited radical quotient. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKTriangular
open EKRadicalQuotient EKElementaryQuotient EKPartitionSpanning EKIntegralBases

def normal (w : List ℕ) : List ℕ :=
  (w.filter (· != 0)).insertionSort (· ≥ ·)

theorem normal_sorted (w : List ℕ) : (normal w).Sorted (· ≥ ·) :=
  List.sorted_insertionSort _ _

theorem normal_positive (w : List ℕ) : ∀ a ∈ normal w, 0 < a := by
  intro a ha
  simp only [normal, List.mem_insertionSort, List.mem_filter, bne_iff_ne, ne_eq] at ha
  omega

theorem normal_perm {w v : List ℕ} (hp : w.Perm v) : normal w = normal v := by
  apply List.eq_of_perm_of_sorted _ (normal_sorted w) (normal_sorted v)
  exact (List.perm_insertionSort _ _).trans
    ((hp.filter _).trans (List.perm_insertionSort _ _).symm)

@[simp] theorem normal_nil : normal [] = [] := rfl
@[simp] theorem normal_cons (a : ℕ) (w : List ℕ) :
    normal (a::w) = if a=0 then normal w else (normal w).orderedInsert (· ≥ ·) a := by
  by_cases ha : a=0 <;> simp [normal, ha]

theorem insert_strictMono (a : ℕ) : StrictMono (List.orderedInsert (· ≥ ·) a) := by
  intro u v huv
  change List.Lex (· < ·) u v at huv
  induction huv with
  | nil =>
    simp only [List.orderedInsert]
    split_ifs with hb
    · exact List.Lex.cons List.Lex.nil
    · exact List.Lex.rel (by omega)
  | @rel b c bs cs hbc =>
    simp only [List.orderedInsert]
    split_ifs <;> first
      | exact List.Lex.cons (List.Lex.rel hbc)
      | exact List.Lex.rel (by omega)
  | @cons b bs cs h ih =>
    simp only [List.orderedInsert]
    split_ifs
    · exact List.Lex.cons (List.Lex.cons h)
    · exact List.Lex.cons ih

theorem normal_prefix_lt (p : List ℕ) {u v : List ℕ}
    (h : normal u < normal v) : normal (p++u) < normal (p++v) := by
  induction p with
  | nil => exact h
  | cons a p ih =>
    simp only [List.cons_append, normal_cons]
    split_ifs
    · exact ih
    · exact insert_strictMono a ih

theorem normal_append_comm (u v : List ℕ) : normal (u++v) = normal (v++u) :=
  normal_perm (List.perm_append_comm)

theorem normal_context_lt (p q : List ℕ) {u v : List ℕ}
    (h : normal u < normal v) : normal (p++u++q) < normal (p++v++q) := by
  simp only [List.append_assoc]
  apply normal_prefix_lt p
  rw [normal_append_comm u q, normal_append_comm v q]
  exact normal_prefix_lt q h

theorem normal_pair_strict {a b u v : ℕ} (hab : a<b) (huv : u+v=a+b) (hu : b<u) :
    normal [a,b] < normal [u,v] := by
  have hv : v<u := by omega
  have hb : b≠0 := by omega
  have hu0 : u≠0 := by omega
  by_cases ha : a=0 <;> by_cases hv0 : v=0 <;>
    simp [normal, ha, hv0, hb, hu0, List.orderedInsert, show ¬ a ≥ b from by omega,
      show u ≥ v from by omega] <;> exact List.Lex.rel hu

theorem normal_pair_le {a b u v : ℕ} (hab : a<b) (huv : u+v=a+b) (hu : b≤u) :
    normal [a,b] ≤ normal [u,v] := by
  rcases eq_or_lt_of_le hu with he | he
  · subst u
    have hv : v=a := by omega
    subst v
    exact le_of_eq (normal_perm (List.Perm.swap _ _ _))
  · exact le_of_lt (normal_pair_strict hab huv he)

theorem normal_context_le (p q : List ℕ) {u v : List ℕ}
    (h : normal u ≤ normal v) : normal (p++u++q) ≤ normal (p++v++q) := by
  rcases eq_or_lt_of_le h with he | he
  · have hp : normal (p++u) = normal (p++v) := by
      induction p with
      | nil => exact he
      | cons a p ih => simp only [List.cons_append, normal_cons, ih]
    have hc : normal (q++(p++u)) = normal (q++(p++v)) := by
      induction q with
      | nil => exact hp
      | cons a q ih => simp only [List.cons_append, normal_cons, ih]
    simpa only [normal_append_comm (p++u) q, normal_append_comm (p++v) q] using le_of_eq hc
  · exact le_of_lt (normal_context_lt p q he)

theorem normal_sum (w : List ℕ) : (normal w).sum = w.sum := by
  rw [normal, (List.perm_insertionSort _ _).sum_eq]
  exact (erase_zeros false w).2

def shape (w : List ℕ) : YoungDiagram := YoungDiagram.ofRowLens (normal w) (normal_sorted w)
@[simp] theorem shape_rows (w : List ℕ) : (shape w).rowLens = normal w :=
  YoungDiagram.rowLens_ofRowLens_eq_self (normal_positive w)
@[simp] theorem shape_card (w : List ℕ) : (shape w).card = w.sum := by
  rw [shape, card_ofRowLens, normal_sum]

theorem normal_of_sorted {w : List ℕ} (hw : w.Sorted (· ≥ ·)) :
    normal w = w.filter (· != 0) := (hw.filter _).insertionSort_eq

theorem normal_partition (μ : YoungDiagram) : normal μ.rowLens = μ.rowLens := by
  rw [normal_of_sorted μ.rowLens_sorted]
  apply List.filter_eq_self.mpr
  intro a ha
  have hp := μ.pos_of_mem_rowLens a ha
  simp only [bne_iff_ne, ne_eq]
  omega

theorem sorted_word_shape {w : List ℕ} (hw : w.Sorted (· ≥ ·)) :
    word false w = hPartition (shape w) := by
  change word false w = word false (shape w).rowLens
  rw [shape_rows, normal_of_sorted hw, (erase_zeros false w).1]

def upperSpan (d : ℕ) (l : List ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ μ : YoungDiagram, μ.card=d ∧ l≤μ.rowLens ∧ hPartition μ=x}
def strictSpan (d : ℕ) (l : List ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ μ : YoungDiagram, μ.card=d ∧ l<μ.rowLens ∧ hPartition μ=x}

theorem upper_mono {d : ℕ} {u v : List ℕ} (h : u≤v) : upperSpan d v ≤ upperSpan d u := by
  apply Submodule.span_mono
  rintro x ⟨μ,hd,hv,rfl⟩
  exact ⟨μ,hd,le_trans h hv,rfl⟩

theorem upper_le_strict {d : ℕ} {u v : List ℕ} (h : u<v) : upperSpan d v ≤ strictSpan d u := by
  apply Submodule.span_mono
  rintro x ⟨μ,hd,hv,rfl⟩
  exact ⟨μ,hd,lt_of_lt_of_le h hv,rfl⟩

/-- General contextual straightening support, not a finite-degree test. -/
theorem word_upper (w : List ℕ) : word false w ∈ upperSpan w.sum (normal w) := by
  induction hc : cost w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rcases sorted_or_ascent w with hw | ⟨p,q,a,b,rfl,hab⟩
    · rw [sorted_word_shape hw]
      exact Submodule.subset_span ⟨shape w, shape_card w, by simp, rfl⟩
    · have hh := pair_mem false (upperSpan (p++a::b::q).sum (normal (p++a::b::q)))
        (word false p) (word false q) a b (by omega) (fun u v huv hu => by
          have hcost := cost_replace p q hab huv hu
          have hm := ih (cost (p++u::v::q)) (by omega) (p++u::v::q) rfl
          have hn : normal (p++a::b::q) ≤ normal (p++u::v::q) := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using
              normal_context_le p q (normal_pair_le hab huv hu)
          have hd : (p++u::v::q).sum=(p++a::b::q).sum := by
            simp only [List.sum_append, List.sum_cons]; omega
          rw [hd] at hm
          have hm' := upper_mono hn hm
          simpa only [word_append, word_cons, mul_assoc] using hm')
      simpa only [word_append, word_cons, mul_assoc] using hh

/-- The exponent acquired when a strict ascent is exchanged. -/
def cross (a b : ℕ) : ℕ := if a<b then a*b+a else 0
def invExp : List ℕ → ℕ
  | [] => 0
  | a::w => (w.map (cross a)).sum + invExp w

theorem invExp_sorted {w : List ℕ} (hw : w.Sorted (· ≥ ·)) : invExp w=0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [invExp, ih hw.of_cons, add_zero]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    have hab := List.rel_of_sorted_cons hw b hb
    simp [cross, show ¬ a<b from by omega]

theorem invExp_swap (p q : List ℕ) {a b : ℕ} (hab : a<b) :
    invExp (p++a::b::q) = invExp (p++b::a::q) + (a*b+a) := by
  induction p with
  | nil =>
    simp only [List.nil_append, invExp, List.map_cons, List.sum_cons]
    simp only [cross, hab, show ¬ b<a from by omega, if_true, if_false]
    omega
  | cons c p ih =>
    simp only [List.cons_append, invExp, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    rw [ih]
    omega

theorem exchange_sign_even (a b : ℕ) (he : Even (a+b)) : (-1 : ℤ)^(a*b+a)=1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  rw [Nat.even_iff] at he
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.add_mod, Nat.mul_mod, ha, hb] at he ⊢

theorem exchange_sign_odd (a b : ℕ) (he : ¬ Even (a+b)) :
    (-1 : ℤ)^(a*b+a)=(-1 : ℤ)^a := by
  rw [neg_one_pow_eq_pow_mod_two (a*b+a), neg_one_pow_eq_pow_mod_two a]
  rw [Nat.even_iff] at he
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp [Nat.add_mod, Nat.mul_mod, ha, hb] at he ⊢

/-- Exact leading coefficient in a context; all outward terms are genuinely
strictly higher, and are the only membership hypotheses. -/
theorem pair_leading (S : Submodule ℤ Q) (L R : Q) (a b : ℕ) (hab : a<b)
    (hh : ∀ u v : ℕ, u+v=a+b → b<u → L*(g false u*g false v)*R ∈ S) :
    L*(g false a*g false b)*R - (-1 : ℤ)^(a*b+a) • (L*(g false b*g false a)*R) ∈ S := by
  by_cases he : Even (a+b)
  · rw [exchange_sign_even a b he, one_smul,
      show g false a*g false b=g false b*g false a from EKQuotientRelations.same_even false a b he,
      sub_self]
    exact S.zero_mem
  · cases a with
    | zero => simp
    | succ a =>
      have hp : Even (a+b) := by rw [Nat.even_iff] at *; omega
      have hX : L*(g false a*g false (b+1))*R ∈ S :=
        pair_mem false S L R a (b+1) (by omega)
          (fun u v huv hu => hh u v (by omega) (by omega))
      have hY := hh (b+1) a (by omega) (by omega)
      have hr := congrArg (fun x : Q => L*x*R)
        (EKQuotientRelations.same_odd_succ false a b hp)
      change L*(g false a*g false (b+1) + (-1 : ℤ)^a • (g false (b+1)*g false a))*R =
        L*((-1 : ℤ)^a • (g false (a+1)*g false b) + g false b*g false (a+1))*R at hr
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc] at hr
      have hm := S.smul_mem ((-1 : ℤ)^a) (S.add_mem hX (S.smul_mem ((-1 : ℤ)^a) hY))
      rw [hr, smul_add, smul_smul, EKAutomorphisms.sign_square, one_smul] at hm
      rw [exchange_sign_odd (a+1) b he, pow_succ, mul_neg_one, neg_smul, sub_neg_eq_add]
      exact hm

theorem shape_perm {w v : List ℕ} (hp : w.Perm v) : shape w=shape v := by
  unfold shape
  congr 1
  exact normal_perm hp

/-- Complete integral straightening with an exact signed leading term. -/
theorem word_leading (w : List ℕ) :
    word false w - (-1 : ℤ)^invExp w • hPartition (shape w) ∈ strictSpan w.sum (normal w) := by
  induction hc : cost w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rcases sorted_or_ascent w with hw | ⟨p,q,a,b,rfl,hab⟩
    · rw [invExp_sorted hw, pow_zero, one_smul, sorted_word_shape hw, sub_self]
      exact Submodule.zero_mem _
    · have hcost := cost_replace p q hab (show b+a=a+b by omega) le_rfl
      have hi := ih (cost (p++b::a::q)) (by omega) (p++b::a::q) rfl
      have hp : (p++a::b::q).Perm (p++b::a::q) :=
        (List.Perm.swap _ _ _).append_left p
      have hd := hp.sum_eq
      have hn := normal_perm hp
      have hs := shape_perm hp
      rw [← hd, ← hn, ← hs] at hi
      have hm := pair_leading (strictSpan (p++a::b::q).sum (normal (p++a::b::q)))
        (word false p) (word false q) a b hab (fun u v huv hu => by
          have hn' : normal (p++a::b::q) < normal (p++u::v::q) := by
            simpa only [List.append_assoc, List.cons_append, List.nil_append] using
              normal_context_lt p q (normal_pair_strict hab huv hu)
          have hd' : (p++u::v::q).sum=(p++a::b::q).sum := by
            simp only [List.sum_append, List.sum_cons]; omega
          have hw := word_upper (p++u::v::q)
          rw [hd'] at hw
          have hh := upper_le_strict hn' hw
          simpa only [word_append, word_cons, mul_assoc] using hh)
      have hm' : word false (p++a::b::q) - (-1 : ℤ)^(a*b+a) • word false (p++b::a::q) ∈
          strictSpan (p++a::b::q).sum (normal (p++a::b::q)) := by
        simpa only [word_append, word_cons, mul_assoc] using hm
      have hh := (strictSpan (p++a::b::q).sum (normal (p++a::b::q))).add_mem hm'
        ((strictSpan (p++a::b::q).sum (normal (p++a::b::q))).smul_mem ((-1 : ℤ)^(a*b+a)) hi)
      rw [smul_sub, smul_smul, sub_add_sub_cancel] at hh
      rw [invExp_swap p q hab, pow_add, mul_comm]
      exact hh

theorem invExp_append_singleton (w : List ℕ) (a : ℕ) :
    invExp (w++[a]) = invExp w + (w.map (fun b => cross b a)).sum := by
  induction w with
  | nil => simp [invExp]
  | cons b w ih =>
    simp only [List.cons_append, invExp, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
    rw [ih]
    omega

theorem cross_parity (a b : ℕ) (hb : b≤a) : (a*b+cross b a)%2=b%2 := by
  rcases lt_or_eq_of_le hb with hb | rfl
  · simp only [cross, hb, if_true]
    rw [Nat.mul_comm a b]
    omega
  · simp only [cross, lt_self_iff_false, if_false, add_zero]
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one b with ha | ha <;> simp [ha]

theorem cross_sum_parity (a : ℕ) (w : List ℕ) (hw : ∀ b∈w, b≤a) :
    (a*w.sum + (w.map (fun b => cross b a)).sum)%2 = w.sum%2 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have hb := cross_parity a b (hw b (by simp))
    have ht := ih (fun c hc => hw c (by simp [hc]))
    simp only [List.sum_cons, List.map_cons]
    have he : a*(b+w.sum)+(cross b a+(w.map (fun b => cross b a)).sum) =
        (a*b+cross b a)+(a*w.sum+(w.map (fun b => cross b a)).sum) := by ring
    rw [he, Nat.add_mod, hb, ht, ← Nat.add_mod]

/-- The super sign and straightening sign combine to the row-index statistic. -/
theorem reversal_sign {w : List ℕ} (hw : w.Sorted (· ≥ ·)) :
    (-1 : ℤ)^(EKAutomorphisms.pairExponent w + invExp w.reverse)=(-1 : ℤ)^(cost w) := by
  suffices he : (EKAutomorphisms.pairExponent w + invExp w.reverse)%2=cost w%2 by
    rw [neg_one_pow_eq_pow_mod_two, he, ← neg_one_pow_eq_pow_mod_two]
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ht := ih hw.of_cons
    have hc := cross_sum_parity a w (List.rel_of_sorted_cons hw)
    simp only [EKAutomorphisms.pairExponent, List.reverse_cons, invExp_append_singleton,
      List.map_reverse, List.sum_reverse, cost]
    have he : a*w.sum + EKAutomorphisms.pairExponent w +
        (invExp w.reverse + (w.map (fun b => cross b a)).sum) =
        (a*w.sum+(w.map (fun b => cross b a)).sum) +
          (EKAutomorphisms.pairExponent w + invExp w.reverse) := by omega
    rw [he, Nat.add_mod, hc, ht, ← Nat.add_mod]

/-- Source notation b(ν)=Σᵢ choose(νᵢ,2), without altering the diagonal. -/
def b (μ : YoungDiagram) : ℕ := (μ.rowLens.map (fun n => n.choose 2)).sum

theorem range_sum_choose (n : ℕ) : (∑ i ∈ Finset.range n, i)=n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

theorem row_cells_disjoint (a : ℕ) (w : List ℕ) :
    Disjoint (({0} : Finset ℕ) ×ˢ Finset.range a)
      ((YoungDiagram.cellsOfRowLens w).map
        (Function.Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Function.Embedding.refl ℕ))) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i,j⟩ hp hq
  simp only [Finset.mem_product, Finset.mem_singleton] at hp
  obtain ⟨rfl,_⟩ := hp
  rcases Finset.mem_map.mp hq with ⟨⟨u,v⟩,_,hh⟩
  have he := congrArg Prod.fst hh
  simp at he

theorem cells_column_sum (w : List ℕ) :
    (∑ p ∈ YoungDiagram.cellsOfRowLens w, p.2)=(w.map (fun n => n.choose 2)).sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.sum_union (row_cells_disjoint a w)]
    simp only [Finset.sum_product, Finset.sum_singleton, Finset.sum_map,
      Function.Embedding.prodMap, Prod.map, Function.Embedding.coeFn_mk, Function.Embedding.refl_apply,
      List.map_cons, List.sum_cons]
    rw [range_sum_choose, ih]

theorem cells_row_sum (w : List ℕ) :
    (∑ p ∈ YoungDiagram.cellsOfRowLens w, p.1)=cost w := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens, cost]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.sum_union (row_cells_disjoint a w)]
    simp only [Finset.sum_product, Finset.sum_singleton, Finset.sum_const_zero,
      zero_add, Finset.sum_map, Function.Embedding.prodMap, Prod.map, Function.Embedding.coeFn_mk]
    simp only [Nat.succ_eq_add_one, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one, ih, card_cellsOfRowLens, cost]
    omega

theorem cells_rows (μ : YoungDiagram) : YoungDiagram.cellsOfRowLens μ.rowLens = μ.cells := by
  exact congrArg YoungDiagram.cells (YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ))

theorem b_eq_cells (μ : YoungDiagram) : b μ = ∑ p ∈ μ.cells, p.2 := by
  rw [b, ← cells_column_sum, cells_rows]

/-- The exact conjugate-partition statistic in Lemma 2.16. -/
theorem b_transpose (μ : YoungDiagram) : b μ.transpose = cost μ.rowLens := by
  rw [b_eq_cells]
  change (∑ p ∈ (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells, p.2)=_
  simp only [Equiv.finsetCongr_apply, Finset.sum_map, Equiv.toEmbedding_apply,
    Equiv.prodComm_apply, Prod.swap]
  rw [← cells_rows μ, cells_row_sum]

theorem shape_partition (μ : YoungDiagram) : shape μ.rowLens=μ := by
  unfold shape
  simp only [normal_partition]
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- EK Lemma 2.16 as a signed leading term plus strictly higher terms. -/
theorem psi3_triangular_remainder (μ : YoungDiagram) :
    EKAutomorphisms.psi3 (hPartition μ) - (-1 : ℤ)^(b μ.transpose) • hPartition μ ∈
      strictSpan μ.card μ.rowLens := by
  have hm := word_leading μ.rowLens.reverse
  have hp := List.reverse_perm μ.rowLens
  rw [List.sum_reverse, rowLens_sum, normal_perm hp, normal_partition,
    shape_perm hp, shape_partition] at hm
  have hh := (strictSpan μ.card μ.rowLens).smul_mem
    ((-1 : ℤ)^(EKAutomorphisms.pairExponent μ.rowLens)) hm
  rw [smul_sub, smul_smul, ← pow_add, reversal_sign μ.rowLens_sorted, ← b_transpose μ] at hh
  change EKAutomorphisms.psi3 ((μ.rowLens.map h).prod) - _ ∈ _
  rw [EKAutomorphisms.psi3_hWord]
  exact hh

/-- Source H_{≥μ} in the actual integral quotient. -/
def Hge (μ : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ ν : YoungDiagram, ν.card=μ.card ∧
    (ν=μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens) ∧ hPartition ν=x}

theorem Hge_eq_upper (μ : YoungDiagram) : Hge μ=upperSpan μ.card μ.rowLens := by
  unfold Hge upperSpan
  apply congrArg (Submodule.span ℤ)
  apply Set.ext
  intro x
  constructor
  · rintro ⟨ν,hd,he | hl,hx⟩
    · subst ν; exact ⟨μ,hd,le_rfl,hx⟩
    · exact ⟨ν,hd,le_of_lt hl,hx⟩
  · rintro ⟨ν,hd,hl,hx⟩
    refine ⟨ν,hd,?_,hx⟩
    rcases eq_or_lt_of_le hl with he | he
    · left
      have hh : μ=ν := by simpa only [shape_partition] using congrArg shape he
      exact hh.symm
    · exact Or.inr he

/-- EK Lemma 2.16, support including the empty partition. -/
theorem psi3_mem_upper (μ : YoungDiagram) :
    EKAutomorphisms.psi3 (hPartition μ) ∈ upperSpan μ.card μ.rowLens := by
  have hh := word_upper μ.rowLens.reverse
  rw [List.sum_reverse, rowLens_sum, normal_perm (List.reverse_perm _), normal_partition] at hh
  change EKAutomorphisms.psi3 ((μ.rowLens.map h).prod) ∈ _
  rw [EKAutomorphisms.psi3_hWord]
  exact (upperSpan μ.card μ.rowLens).smul_mem _ hh

theorem psi3_mem_Hge (μ : YoungDiagram) : EKAutomorphisms.psi3 (hPartition μ) ∈ Hge μ := by
  rw [Hge_eq_upper]
  exact psi3_mem_upper μ

theorem upper_coordinate_zero {d : ℕ} {l : List ℕ} {x : Q}
    (hx : x ∈ upperSpan d l) (ν : YoungDiagram) (hn : ν.card≠d ∨ ¬ l≤ν.rowLens) :
    hBasis.repr x ν=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ,hd,hl,rfl⟩ := hx
    have hne : μ≠ν := by
      intro he
      subst ν
      rcases hn with hn | hn
      · exact hn hd
      · exact hn hl
    simp [h_coordinates_partition, hne]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, map_zsmul, Finsupp.smul_apply, smul_eq_mul, hx, mul_zero]

theorem strict_coordinate_zero {d : ℕ} {l : List ℕ} {x : Q}
    (hx : x ∈ strictSpan d l) (ν : YoungDiagram) (hn : ν.rowLens≤l) :
    hBasis.repr x ν=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ,_,hl,rfl⟩ := hx
    have hne : μ≠ν := by
      intro he
      subst ν
      exact (not_lt_of_ge hn) hl
    simp [h_coordinates_partition, hne]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, map_zsmul, Finsupp.smul_apply, smul_eq_mul, hx, mul_zero]

/-- The leading coefficient is the specified source sign, not a chosen unit. -/
theorem psi3_diagonal (μ : YoungDiagram) :
    hBasis.repr (EKAutomorphisms.psi3 (hPartition μ)) μ=(-1 : ℤ)^(b μ.transpose) := by
  have he := strict_coordinate_zero (psi3_triangular_remainder μ) μ le_rfl
  simpa only [map_sub, map_smul, h_coordinates_partition, Finsupp.sub_apply,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, sub_eq_zero] using he

/-- Every nonzero coordinate has the original degree and is lexicographically
at or above the input partition. -/
theorem psi3_coordinate_support (μ ν : YoungDiagram)
    (hn : hBasis.repr (EKAutomorphisms.psi3 (hPartition μ)) ν≠0) :
    ν.card=μ.card ∧ μ.rowLens≤ν.rowLens := by
  constructor
  · by_contra hd
    exact hn (upper_coordinate_zero (psi3_mem_upper μ) ν (Or.inl hd))
  · by_contra hl
    exact hn (upper_coordinate_zero (psi3_mem_upper μ) ν (Or.inr hl))

/-- A finite correction supported strictly above μ. All coefficients are
literal integral h-basis coordinates, on the left as scalar multiples. -/
theorem psi3_expansion (μ : YoungDiagram) :
    ∃ a : YoungDiagram →₀ ℤ,
      EKAutomorphisms.psi3 (hPartition μ) =
        (-1 : ℤ)^(b μ.transpose) • hPartition μ + a.sum (fun ν z => z • hPartition ν) ∧
      (∀ ν, a ν≠0 → ν.card=μ.card ∧ List.Lex (· < ·) μ.rowLens ν.rowLens) := by
  classical
  let c := hBasis.repr (EKAutomorphisms.psi3 (hPartition μ))
  refine ⟨c.erase μ, ?_, ?_⟩
  · have he := congrArg (fun z => hBasis.repr.symm z) (Finsupp.erase_add_single μ c)
    dsimp only at he
    rw [map_add, Basis.repr_symm_single, hBasis_apply] at he
    change hBasis.repr.symm (c.erase μ) +
      hBasis.repr (EKAutomorphisms.psi3 (hPartition μ)) μ • hPartition μ = _ at he
    rw [psi3_diagonal] at he
    have hs : hBasis.repr.symm (c.erase μ) = (c.erase μ).sum (fun ν z => z • hPartition ν) := by
      simp only [Basis.repr_symm_apply, Finsupp.linearCombination_apply, hBasis_apply]
    rw [hs] at he
    simpa only [c, LinearEquiv.symm_apply_apply, add_comm] using he.symm
  · intro ν hn
    have hne : ν≠μ := by intro he; subst ν; simp at hn
    have hc : c ν≠0 := by simpa [Finsupp.erase_ne hne] using hn
    obtain ⟨hd,hl⟩ := psi3_coordinate_support μ ν hc
    refine ⟨hd, lt_of_le_of_ne hl ?_⟩
    intro he
    apply hne
    have hdiag : μ=ν := by
      simpa only [shape_partition] using congrArg shape he
    exact hdiag.symm

/-- Arbitrary-degree triangular-matrix consumer over the existing exhaustive
DegreeShape index; no finite rank cutoff is assumed. -/
theorem degree_matrix_consumer (d : ℕ) (μ ν : DegreeShapes.DegreeShape d) :
    hBasis.repr (EKAutomorphisms.psi3 (hPartition μ.val)) μ.val=(-1 : ℤ)^(b μ.val.transpose) ∧
    (List.Lex (· < ·) ν.val.rowLens μ.val.rowLens →
      hBasis.repr (EKAutomorphisms.psi3 (hPartition μ.val)) ν.val=0) := by
  refine ⟨psi3_diagonal μ.val, ?_⟩
  intro hlt
  exact upper_coordinate_zero (psi3_mem_upper μ.val) ν.val (Or.inr (not_le_of_gt hlt))

/-- Coordinates outside the frozen same-degree, equality-or-strict-lex
support are zero; this includes every wrong-degree coordinate. -/
theorem psi3_coordinate_zero (μ ν : YoungDiagram)
    (hout : ν.card≠μ.card ∨ ¬ (ν=μ ∨ List.Lex (· < ·) μ.rowLens ν.rowLens)) :
    hBasis.repr (EKAutomorphisms.psi3 (hPartition μ)) ν=0 := by
  by_contra hn
  obtain ⟨hd,hl⟩ := psi3_coordinate_support μ ν hn
  rcases hout with hout | hout
  · exact hout hd
  · apply hout
    rcases eq_or_lt_of_le hl with he | he
    · left
      have hh : μ=ν := by simpa only [shape_partition] using congrArg shape he
      exact hh.symm
    · exact Or.inr he

end OddMath.Frontier.EKTriangular
