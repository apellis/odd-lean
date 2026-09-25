import OddMath.Frontier.ElementaryGeneration
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Defs

/-! Integral graded elementary basis: EKL 1111.1320v1, Prop. 2.2.
The index records ROW lengths; the literal product uses descending COLUMN
heights. Polynomial degree d is paper degree 2d. Only ranks N=n+2 are claimed. -/
namespace OddMath.Frontier.ElementaryBasis
open OddMath.SkewPolynomial (SkewPolynomial monomial expSingle)
open ElementaryGeneration OddSymmetricKernel FiniteCompleteElementary
open scoped BigOperators

abbrev weight {N : ℕ} (a : Exp N) : ℕ := ∑ i, a i

def height {N : ℕ} (a : Exp N) : ℕ := (Finset.univ.filter (fun i => 0 < a i)).card

def predRows {N : ℕ} (a : Exp N) : Exp N := fun i => a i - 1

def columnsAux {N : ℕ} : ℕ → Exp N → List ℕ
  | 0, _ => []
  | d+1, a => if height a = 0 then [] else height a :: columnsAux d (predRows a)

/-- Deterministic Ferrers conjugation, stripping the leftmost column first. -/
def columns {N : ℕ} (a : Exp N) : List ℕ := columnsAux (weight a) a

 theorem height_le {N : ℕ} (a : Exp N) : height a ≤ N :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin N)

 theorem height_zero {N : ℕ} (a : Exp N) : height a = 0 ↔ a = 0 := by
  simp only [height, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; have := h (Finset.mem_univ i); exact Nat.eq_zero_of_not_pos this
  · intro h i _; simp [h]

 theorem height_pred_le {N : ℕ} (a : Exp N) : height (predRows a) ≤ height a := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, predRows] at *
  omega

 theorem pred_weight_lt {N : ℕ} (a : Exp N) (h : height a ≠ 0) :
    weight (predRows a) < weight a := by
  apply Finset.sum_lt_sum
  · intro i _; exact Nat.sub_le _ _
  · have hp : ∃ i, 0 < a i := by
      by_contra hh
      apply h
      apply (height_zero a).mpr
      funext i
      have hi : ¬ 0 < a i := fun hi => hh ⟨i,hi⟩
      exact Nat.eq_zero_of_not_pos hi
    obtain ⟨i,hi⟩ := hp
    exact ⟨i, Finset.mem_univ _, Nat.sub_lt hi (by decide)⟩

 theorem height_prefix {N : ℕ} (a : Exp N) (ha : Antitone a) :
    prefixExp N (height a) + predRows a = a := by
  obtain ⟨k,hk,h⟩ := positive_prefix a ha
  have he : height a = k := by
    unfold height
    have hh : Finset.univ.filter (fun i : Fin N => 0 < a i) =
        Finset.univ.filter (fun i => i.val < k) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (h i).symm
    rw [hh]
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hk
  funext i
  simp only [Pi.add_apply, prefixExp, predRows, he]
  by_cases hi : 0 < a i
  · rw [if_pos ((h i).mpr hi)]; omega
  · rw [if_neg (fun hh => hi ((h i).mp hh))]; omega

 theorem columnsAux_valid {N : ℕ} (d : ℕ) (a : Exp N) :
    ∀ k ∈ columnsAux d a, 1 ≤ k ∧ k ≤ height a := by
  induction d generalizing a with
  | zero => simp [columnsAux]
  | succ d ih =>
    simp only [columnsAux]
    split_ifs with h
    · simp
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨Nat.one_le_iff_ne_zero.mpr h, le_rfl⟩
      · exact ⟨(ih _ _ hk).1, (ih _ _ hk).2.trans (height_pred_le a)⟩

 theorem columnsAux_descending {N : ℕ} (d : ℕ) (a : Exp N) :
    (columnsAux d a).Pairwise (· ≥ ·) := by
  induction d generalizing a with
  | zero => simp [columnsAux]
  | succ d ih =>
    simp only [columnsAux]
    split_ifs
    · simp
    · apply List.pairwise_cons.mpr
      exact ⟨fun k hk => (columnsAux_valid d (predRows a) k hk).2.trans (height_pred_le a), ih _⟩

 theorem columns_descending {N : ℕ} (a : Exp N) : (columns a).Pairwise (· ≥ ·) :=
  columnsAux_descending _ _

 theorem columns_valid {N : ℕ} (a : Exp N) : ∀ k ∈ columns a, 1 ≤ k ∧ k ≤ N :=
  fun k hk => ⟨(columnsAux_valid _ _ k hk).1,
    (columnsAux_valid _ _ k hk).2.trans (height_le a)⟩

 theorem columnsAux_exponent {N : ℕ} (d : ℕ) (a : Exp N)
    (ha : Antitone a) (hd : weight a ≤ d) : columnExponent N (columnsAux d a) = a := by
  induction d generalizing a with
  | zero =>
    have hz : a = 0 := by
      funext i
      have hi : a i ≤ weight a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have : a i = 0 := by omega
      exact this
    simp [columnsAux, columnExponent, hz]
  | succ d ih =>
    simp only [columnsAux]
    split_ifs with h
    · simp [columnExponent, (height_zero a).mp h]
    · have hl := pred_weight_lt a h
      have hp : Antitone (predRows a) := fun _ _ hij => Nat.sub_le_sub_right (ha hij) 1
      have he := ih (predRows a) hp (by omega)
      change prefixExp N (height a) + columnExponent N (columnsAux d (predRows a)) = a
      rw [he]; exact height_prefix a ha

 theorem columns_exponent {N : ℕ} (a : Exp N) (ha : Antitone a) :
    columnExponent N (columns a) = a := columnsAux_exponent _ _ ha le_rfl

noncomputable section

/-- Coefficient support definition: no quotient or dimension surrogate. -/
def Homogeneous {N : ℕ} (d : ℕ) (f : SkewPolynomial N) : Prop :=
  ∀ a, weight a ≠ d → f a = 0

 theorem homogeneous_zero {N d : ℕ} : Homogeneous d (0 : SkewPolynomial N) := by
  intro a _; rfl
 theorem homogeneous_add {N d : ℕ} {f g : SkewPolynomial N}
    (hf : Homogeneous d f) (hg : Homogeneous d g) : Homogeneous d (f+g) := by
  intro a ha; simp [hf a ha, hg a ha]
 theorem homogeneous_smul {N d : ℕ} (z : ℤ) {f : SkewPolynomial N}
    (hf : Homogeneous d f) : Homogeneous d (z • f) := by
  intro a ha; rw [Finsupp.smul_apply, hf a ha, smul_zero]
 theorem homogeneous_sub {N d : ℕ} {f g : SkewPolynomial N}
    (hf : Homogeneous d f) (hg : Homogeneous d g) : Homogeneous d (f-g) := by
  intro a ha; simp [hf a ha, hg a ha]

/-- Degree-d joint kernel as a literal submodule of skew polynomials. -/
def degreePiece (n d : ℕ) : Submodule ℤ (SkewPolynomial (n+2)) where
  carrier := {f | f ∈ kernelSubring n ∧ Homogeneous d f}
  zero_mem' := ⟨(kernelSubring n).zero_mem, homogeneous_zero⟩
  add_mem' hf hg := ⟨(kernelSubring n).add_mem hf.1 hg.1, homogeneous_add hf.2 hg.2⟩
  smul_mem' z _ hf := ⟨(kernelSubring n).zsmul_mem hf.1 z, homogeneous_smul z hf.2⟩

 theorem homogeneous_monomial {N : ℕ} (a : Exp N) (c : ℤ) :
    Homogeneous (weight a) (monomial a c) := by
  intro b hb
  exact Finsupp.single_eq_of_ne (fun h => hb (congrArg weight h.symm))

 theorem homogeneous_mul {N d e : ℕ} {f g : SkewPolynomial N}
    (hf : Homogeneous d f) (hg : Homogeneous e g) : Homogeneous (d+e) (f*g) := by
  classical
  intro a ha
  rw [mul_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  apply if_neg
  intro h
  have hud : weight u = d := by by_contra hh; exact Finsupp.mem_support_iff.mp hu (hf u hh)
  have hve : weight v = e := by by_contra hh; exact Finsupp.mem_support_iff.mp hv (hg v hh)
  apply ha
  rw [← h]
  simpa only [weight, Pi.add_apply, Finset.sum_add_distrib] using congrArg₂ (·+·) hud hve

 theorem homogeneous_sum {N d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → SkewPolynomial N)
    (h : ∀ i ∈ s, Homogeneous d (f i)) : Homogeneous d (∑ i ∈ s, f i) := by
  intro a ha
  simp only [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero (fun i hi => h i hi a ha)

 theorem weight_exponents {N : ℕ} (w : List (Fin N)) :
    weight (PbwRealization.exponents w) = w.length := by
  induction w with
  | nil => simp [PbwRealization.exponents_nil]
  | cons i w ih =>
    rw [PbwRealization.exponents_cons]
    simp only [weight, Pi.add_apply, Finset.sum_add_distrib]
    simp [expSingle, ih, Nat.add_comm]

 theorem elementary_homogeneous (N k : ℕ) : Homogeneous k (elementaryPoly N k) := by
  classical
  apply homogeneous_sum
  intro f _
  split_ifs with h
  · obtain ⟨c,_,hc⟩ := tildeWord_monomial (List.ofFn f)
    simp only [List.map_ofFn, Function.comp_def] at hc
    rw [hc]
    have hh := homogeneous_monomial (PbwRealization.exponents (List.ofFn f)) c
    simpa only [weight_exponents, List.length_ofFn] using hh
  · exact homogeneous_zero

 theorem word_homogeneous (N : ℕ) (w : List ℕ) :
    Homogeneous w.sum (elementaryWord N w) := by
  induction w with
  | nil =>
    change Homogeneous 0 (monomial (0 : Exp N) 1)
    simpa only [weight, Pi.zero_apply, Finset.sum_const_zero] using homogeneous_monomial (0 : Exp N) 1
  | cons k w ih => exact homogeneous_mul (elementary_homogeneous N k) ih

 theorem word_leading (N : ℕ) (w : List ℕ) (hw : ∀ k ∈ w, k ≤ N) :
    ∃ c : ℤ, c*c=1 ∧ Leading (elementaryWord N w) (columnExponent N w) c := by
  induction w with
  | nil => exact ⟨1,by norm_num, bounded_single 0 1, Finsupp.single_eq_same⟩
  | cons k w ih =>
    obtain ⟨c,hc,hl⟩ := ih (fun j hj => hw j (by simp [hj]))
    obtain ⟨e,he,hel⟩ := elementary_leading N k (hw k (by simp))
    refine ⟨e*c*OddMath.skewSign (prefixExp N k) (columnExponent N w), ?_, leading_mul hel hl⟩
    calc
      _ = (e*e)*(c*c)*(OddMath.skewSign (prefixExp N k) (columnExponent N w)*
        OddMath.skewSign (prefixExp N k) (columnExponent N w)) := by ring
      _ = 1 := by rw [he,hc,skewSign_square]; norm_num

 theorem columns_leading {N : ℕ} (a : Exp N) (ha : Antitone a) :
    ∃ c : ℤ, c*c=1 ∧ Leading (elementaryWord N (columns a)) a c := by
  simpa only [columns_exponent a ha] using
    word_leading N (columns a) (fun k hk => (columns_valid a k hk).2)

 theorem columns_sum {N : ℕ} (a : Exp N) (ha : Antitone a) : (columns a).sum = weight a := by
  obtain ⟨c,hc,hl⟩ := columns_leading a ha
  by_contra h
  have hz := word_homogeneous N (columns a) a (Ne.symm h)
  rw [hl.2] at hz
  rw [hz] at hc
  norm_num at hc

 theorem columns_homogeneous {N : ℕ} (a : Exp N) (ha : Antitone a) :
    Homogeneous (weight a) (elementaryWord N (columns a)) := by
  rw [← columns_sum a ha]; exact word_homogeneous _ _

abbrev Index (N d : ℕ) := {a : Exp N // Antitone a ∧ weight a = d}

instance indexFinite (N d : ℕ) : Finite (Index N d) := by
  let encode : Index N d → (Fin N → Fin (d+1)) := fun a i => ⟨a.1 i, by
    have h : a.1 i ≤ weight a.1 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [a.2.2] at h; omega⟩
  apply Finite.of_injective encode
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance indexFintype (N d : ℕ) : Fintype (Index N d) := Fintype.ofFinite _

/-- The literal ordered product, with no diagonal rescaling. -/
def basisVector (n d : ℕ) (a : Index (n+2) d) : degreePiece n d :=
  ⟨elementaryWord (n+2) (columns a.1),
    elementaryClosure_le_kernel n (elementaryWord_mem n _ (columns_valid a.1)),
    by simpa only [a.2.2] using columns_homogeneous a.1 a.2.1⟩

 theorem basisVector_leading (n d : ℕ) (a : Index (n+2) d) :
    ∃ c : ℤ, c*c=1 ∧ Leading (basisVector n d a).1 a.1 c := columns_leading a.1 a.2.1

 theorem basisVector_independent (n d : ℕ) : LinearIndependent ℤ (basisVector n d) := by
  classical
  apply LinearIndependent.of_comp (degreePiece n d).subtype
  apply linearIndependent_iff'.mpr
  intro s z hz i hi
  by_contra hzi
  let t := s.filter (fun a => z a ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi,hzi⟩⟩
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image t (fun a => toLex a.1) ht
  obtain ⟨c,hc,hl⟩ := basisVector_leading n d a
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; norm_num at hc
  have he := congrArg (fun f : SkewPolynomial (n+2) => f a.1) hz
  change (∑ b ∈ s, z b • (basisVector n d b).1) a.1 = 0 at he
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single a] at he
  · rw [Finsupp.smul_apply] at he
    change z a * (basisVector n d a).1 a.1 = 0 at he
    rw [hl.2] at he
    exact (Finset.mem_filter.mp ha).2 ((mul_eq_zero.mp he).resolve_right hc0)
  · intro b hb hba
    by_cases hzb : z b = 0
    · rw [hzb, zero_smul]; rfl
    · have hle := hmax b (Finset.mem_filter.mpr ⟨hb,hzb⟩)
      obtain ⟨_,_,hbl⟩ := basisVector_leading n d b
      have hzero : (basisVector n d b).1 a.1 = 0 := by
        by_contra hne
        have hab := hbl.1 a.1 hne
        have hab' : toLex a.1 = toLex b.1 := le_antisymm hab hle
        exact hba (Subtype.ext hab'.symm)
      rw [Finsupp.smul_apply, hzero, smul_zero]
  · intro has
    exact False.elim (has (Finset.mem_filter.mp ha).1)

/-- Integral triangular elimination inside the actual homogeneous joint kernel.
The correcting scalar is an integer, since the diagonal squares to one. -/
 theorem basisVector_spanning (n d : ℕ) :
    ⊤ ≤ Submodule.span ℤ (Set.range (basisVector n d)) := by
  classical
  let S := Submodule.span ℤ (Set.range (basisVector n d))
  have elimination : ∀ A : Lex (Exp (n+2)), ∀ g : degreePiece n d,
      Bounded g.1 (ofLex A) → g ∈ S := by
    intro A
    induction A using WellFoundedLT.induction with
    | ind A ih =>
      intro g hg
      by_cases hz : g.1 = 0
      · have h : g=0 := Subtype.ext hz
        rw [h]; exact S.zero_mem
      obtain ⟨a,ha,hl⟩ := exists_leading g.1 hz
      have hale : toLex a ≤ A := hg a ha
      by_cases hlt : toLex a < A
      · exact ih (toLex a) hlt g hl.1
      have haeq : toLex a = A := le_antisymm hale (le_of_not_gt hlt)
      have had : weight a = d := by
        by_contra h; exact ha (g.2.2 a h)
      let ai : Index (n+2) d := ⟨a,kernel_leading_antitone g.1 g.2.1 a hl.1 ha,had⟩
      let p := basisVector n d ai
      obtain ⟨c,hc,hp⟩ := basisVector_leading n d ai
      let z : ℤ := g.1 a*c
      let r : degreePiece n d := g-z • p
      have hpmem : p ∈ S := Submodule.subset_span ⟨ai,rfl⟩
      have hra : r.1 a = 0 := by
        change g.1 a - (z • p.1) a = 0
        rw [Finsupp.smul_apply]
        change g.1 a - z*p.1 a = 0
        rw [hp.2]
        dsimp [z]
        rw [mul_assoc,hc,mul_one,sub_self]
      have hrbounded : Bounded r.1 a :=
        bounded_add hl.1 (bounded_neg (bounded_smul z hp.1))
      have hrmem : r ∈ S := by
        by_cases hrzero : r.1 = 0
        · have h : r=0 := Subtype.ext hrzero
          rw [h]; exact S.zero_mem
        obtain ⟨b,hb,hbl⟩ := exists_leading r.1 hrzero
        have hba := hrbounded b hb
        have hne : b ≠ a := by intro h; subst b; exact hb hra
        have hlt : toLex b < A := by rw [← haeq]; exact lt_of_le_of_ne hba hne
        exact ih (toLex b) hlt r hbl.1
      have hfinish := S.add_mem hrmem (S.smul_mem z hpmem)
      simpa only [r,sub_add_cancel] using hfinish
  intro g _
  by_cases hz : g.1=0
  · have h : g=0 := Subtype.ext hz
    rw [h]; exact S.zero_mem
  obtain ⟨a,_,hl⟩ := exists_leading g.1 hz
  exact elimination (toLex a) g hl.1

/-- An actual integral basis, not a rank-equality or mod-two lifting argument. -/
noncomputable def gradedBasis (n d : ℕ) : Basis (Index (n+2) d) ℤ (degreePiece n d) :=
  Basis.mk (basisVector_independent n d) (basisVector_spanning n d)

 theorem gradedBasis_apply (n d : ℕ) (a : Index (n+2) d) :
    ((gradedBasis n d a : degreePiece n d) : SkewPolynomial (n+2)) =
      elementaryWord (n+2) (columns a.1) := by
  rw [gradedBasis, Basis.mk_apply]; rfl

 theorem graded_rank (n d : ℕ) :
    Module.finrank ℤ (degreePiece n d) = Fintype.card (Index (n+2) d) :=
  Module.finrank_eq_card_basis (gradedBasis n d)

/-- Multiplicity of a column of height j+1. Its weight is j+1, not j. -/
abbrev Multiplicities (N d : ℕ) := {m : Exp N // ∑ j, (j.val+1)*m j = d}

def rowsOf {N : ℕ} (m : Exp N) : Exp N := fun i => ∑ j ∈ Finset.Ici i, m j

def multiplicitiesOf : {N : ℕ} → Exp N → Exp N
  | 0, _ => fun i => Fin.elim0 i
  | N+1, a => Fin.lastCases (a (Fin.last N)) (fun i => a i.castSucc - a i.succ)

 theorem rowsOf_antitone {N : ℕ} (m : Exp N) : Antitone (rowsOf m) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset
  intro k hk
  exact Finset.mem_Ici.mpr (hij.trans (Finset.mem_Ici.mp hk))

 theorem rowsOf_last {N : ℕ} (m : Exp (N+1)) : rowsOf m (Fin.last N) = m (Fin.last N) := by
  have h : Finset.Ici (Fin.last N) = {Fin.last N} := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm (Fin.le_last j) h, fun h => by rw [h]⟩
  simp [rowsOf, h]

 theorem rowsOf_step {N : ℕ} (m : Exp (N+1)) (i : Fin N) :
    rowsOf m i.castSucc = m i.castSucc + rowsOf m i.succ := by
  have h : Finset.Ici i.castSucc = insert i.castSucc (Finset.Ici i.succ) := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_insert]
    constructor
    · intro hj
      by_cases he : j=i.castSucc
      · exact Or.inl he
      · right; apply Fin.le_iff_val_le_val.mpr
        have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
        have hh : i.val ≤ j.val := hj
        simp only [Fin.val_succ]; omega
    · rintro (rfl|hj)
      · exact le_rfl
      · exact (Fin.castSucc_le_succ i).trans hj
  have hn : i.castSucc ∉ Finset.Ici i.succ := by
    simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]; omega
  simp only [rowsOf, h, Finset.sum_insert hn]

 theorem multiplicitiesOf_rowsOf {N : ℕ} (m : Exp N) : multiplicitiesOf (rowsOf m) = m := by
  cases N with
  | zero => exact Subsingleton.elim _ _
  | succ N =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [multiplicitiesOf, rowsOf_last]
    · simp [multiplicitiesOf, rowsOf_step]

 theorem rowsOf_multiplicitiesOf {N : ℕ} (a : Exp N) (ha : Antitone a) :
    rowsOf (multiplicitiesOf a) = a := by
  cases N with
  | zero => exact Subsingleton.elim _ _
  | succ N =>
    funext i
    induction i using Fin.reverseInduction with
    | last => simp [rowsOf_last, multiplicitiesOf]
    | cast j ih =>
      rw [rowsOf_step, ih]
      simp only [multiplicitiesOf, Fin.lastCases_castSucc]
      exact Nat.sub_add_cancel (ha (Fin.castSucc_le_succ j))

 theorem weight_rowsOf {N : ℕ} (m : Exp N) : weight (rowsOf m) = ∑ j, (j.val+1)*m j := by
  classical
  simp only [weight, rowsOf, ← Finset.sum_filter]
  have h : ∀ i : Fin N, (Finset.univ.filter (fun j => i ≤ j)) = Finset.Ici i := by
    intro i; ext j; simp
  simp_rw [← h, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  have hh : Finset.univ.filter (fun i : Fin N => i ≤ j) = Finset.Iic j := by
    ext i; simp
  rw [hh, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
  simp

 theorem multiplicities_weight {N : ℕ} (a : Exp N) (ha : Antitone a) :
    (∑ j, (j.val+1)*multiplicitiesOf a j) = weight a := by
  rw [← weight_rowsOf, rowsOf_multiplicitiesOf a ha]

/-- Explicit inverse maps: row differences and cumulative column multiplicities. -/
def multiplicityEquiv (N d : ℕ) : Index N d ≃ Multiplicities N d where
  toFun a := ⟨multiplicitiesOf a.1, (multiplicities_weight a.1 a.2.1).trans a.2.2⟩
  invFun m := ⟨rowsOf m.1, rowsOf_antitone m.1, (weight_rowsOf m.1).trans m.2⟩
  left_inv a := Subtype.ext (rowsOf_multiplicitiesOf a.1 a.2.1)
  right_inv m := Subtype.ext (multiplicitiesOf_rowsOf m.1)

noncomputable instance multiplicitiesFintype (N d : ℕ) : Fintype (Multiplicities N d) :=
  Fintype.ofEquiv (Index N d) (multiplicityEquiv N d)

/-- Degreewise coefficient form of the product ∏ (1-q^(2j))⁻¹ in EKL (2.28).
No formal power-series identity or rank-zero/one kernel API is claimed here. -/
 theorem graded_rank_product_coefficient (n d : ℕ) :
    Module.finrank ℤ (degreePiece n d) = Fintype.card (Multiplicities (n+2) d) := by
  rw [graded_rank]
  exact Fintype.card_congr (multiplicityEquiv (n+2) d)

end
end OddMath.Frontier.ElementaryBasis
