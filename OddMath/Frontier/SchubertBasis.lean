import OddMath.Frontier.OddSchubertAction
import OddMath.Frontier.StaircaseLeft

/-! EKL1111.1320v1 Lemma 2.12. Actual integer polynomials and literal chosen words. -/
namespace OddMath.Frontier.SchubertBasis
open OddMath.SkewPolynomial (SkewPolynomial monomial generator expSingle)
open StaircaseSpanning NilCoxeterWords OddSchubertAction AllRankDivided
open scoped BigOperators
noncomputable section

/-- The literal H of (2.46). -/
def H (N : ℕ) : Submodule ℤ (SkewPolynomial N) :=
  Submodule.span ℤ (Set.range (stairMonomial (N := N)))

/-- Coordinatewise bounds, not lexicographic leading bounds. -/
def Box {N : ℕ} (b : Fin N → ℕ) : Submodule ℤ (SkewPolynomial N) :=
  Finsupp.supported ℤ ℤ {a | ∀ i, a i ≤ b i}

theorem mem_box {N : ℕ} (b : Fin N → ℕ) (f : SkewPolynomial N) :
    f ∈ Box b ↔ ∀ a, f a ≠ 0 → ∀ i, a i ≤ b i := by
  simp [Box, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff]

theorem monomial_mem_box {N : ℕ} (a b : Fin N → ℕ) (c : ℤ)
    (h : ∀ i, a i ≤ b i) : monomial a c ∈ Box b := by
  rw [mem_box]
  intro d hd
  have he : a = d := by
    by_contra hn
    exact hd (Finsupp.single_eq_of_ne hn)
  simpa only [← he] using h

theorem H_eq_box (N : ℕ) : H N = Box (fun i => N-1-i.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact monomial_mem_box _ _ _ a.property
  · intro f hf
    rw [mem_box] at hf
    have he : f = ∑ a ∈ f.support, f a • monomial a 1 := by
      simpa only [Finsupp.sum, monomial, Finsupp.smul_single, smul_eq_mul, mul_one] using (Finsupp.sum_single f).symm
    rw [he]
    apply (H N).sum_mem
    intro a ha
    exact (H N).smul_mem _ (Submodule.subset_span ⟨⟨a, hf a (Finsupp.mem_support_iff.mp ha)⟩, rfl⟩)

/-- Multiplication adds coordinate bounds even though its coefficients are skew-signed. -/
theorem box_mul {N : ℕ} {a b : Fin N → ℕ} {f g : SkewPolynomial N}
    (hf : f ∈ Box a) (hg : g ∈ Box b) : f*g ∈ Box (a+b) := by
  have hf' := (mem_box a f).mp hf
  have hg' := (mem_box b g).mp hg
  change f.sum (fun x c => g.sum (fun y d => monomial (x+y) (c*d*OddMath.skewSign x y))) ∈ _
  apply (Box (a+b)).sum_mem
  intro x hx
  apply (Box (a+b)).sum_mem
  intro y hy
  apply monomial_mem_box
  intro i
  exact Nat.add_le_add (hf' x (Finsupp.mem_support_iff.mp hx) i)
    (hg' y (Finsupp.mem_support_iff.mp hy) i)

theorem box_mono {N : ℕ} {a b : Fin N → ℕ} (h : ∀ i, a i ≤ b i) : Box a ≤ Box b := by
  intro f hf
  exact (mem_box _ _).mpr (fun x hx i => (mem_box _ _).mp hf x hx i |>.trans (h i))

def twice {N : ℕ} (i : Fin N) : Fin N → ℕ := expSingle i + expSingle i

@[simp] theorem twice_apply {N : ℕ} (i j : Fin N) : twice i j = if i=j then 2 else 0 := by
  by_cases h : i=j <;> simp [twice, expSingle, h]

theorem square_monomial {N : ℕ} (i : Fin N) (a : Fin N → ℕ) (c : ℤ) :
    generator i ^ 2 * monomial a c = monomial (twice i + a) c := by
  have hsame : OddMath.skewSign (expSingle i) (expSingle i) = 1 := by
    have hz : OddMath.crossingCount (expSingle i) (expSingle i) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro k hk
      have hkj := (Finset.mem_filter.mp hk).2
      by_cases hij : i=j
      · subst j
        simp [expSingle, ne_of_gt hkj]
      · simp [expSingle, hij]
    rw [OddMath.skewSign, hz, pow_zero]
  have hsign : OddMath.skewSign (twice i) a = 1 := by
    simp only [twice, OddMath.skewSign, OddMath.crossingCount_add_left, pow_add]
    exact ElementaryGeneration.skewSign_square _ _
  rw [pow_two]
  change OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.mul (monomial (expSingle i) 1) (monomial (expSingle i) 1))
    (monomial a c) = _
  rw [OddMath.SkewPolynomial.mul_monomial, hsame]
  simp only [one_mul]
  rw [OddMath.SkewPolynomial.mul_monomial]
  change monomial (twice i + a) (1*c*OddMath.skewSign (twice i) a) = _
  rw [hsign]
  simp

theorem square_coeff_same {N : ℕ} (i : Fin N) (f : SkewPolynomial N) (a : Fin N → ℕ) :
    (generator i ^ 2 * f) (twice i + a) = f a := by
  classical
  have he := (Finsupp.sum_single f).symm
  conv_lhs => rw [he]
  simp only [Finsupp.sum, Finset.mul_sum, square_monomial, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single a]
  · exact Finsupp.single_eq_same
  · intro b _ hba
    exact Finsupp.single_eq_of_ne (fun h => hba (add_left_cancel h))
  · intro ha
    simp [Finsupp.not_mem_support_iff.mp ha]

theorem square_coeff_nonzero {N : ℕ} (i : Fin N) (f : SkewPolynomial N) (a : Fin N → ℕ)
    (ha : (generator i ^ 2 * f) a ≠ 0) :
    ∃ b, f b ≠ 0 ∧ twice i + b = a := by
  classical
  have he := (Finsupp.sum_single f).symm
  rw [he] at ha
  simp only [Finsupp.sum, Finset.mul_sum, square_monomial, Finsupp.finset_sum_apply] at ha
  obtain ⟨b,hb,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  refine ⟨b, Finsupp.mem_support_iff.mp hb, ?_⟩
  by_contra hn
  exact hc (Finsupp.single_eq_of_ne hn)

/-- Extremal-support cancellation: the square difference cannot hide a bound violation.
This avoids the false assertion that every individual exponent decreases under ∂. -/
theorem square_difference_bound {N : ℕ} (p q k : Fin N) (hpq : p ≠ q)
    (hk : k = p ∨ (k ≠ p ∧ k ≠ q)) (f : SkewPolynomial N) (B : ℕ)
    (h : ∀ a, ((generator p ^ 2 - generator q ^ 2) * f) a ≠ 0 → a k ≤ B) :
    ∀ a, f a ≠ 0 → a k + (if k=p then 2 else 0) ≤ B := by
  classical
  intro a ha
  by_contra hbad
  let bad := f.support.filter (fun a => B < a k + (if k=p then 2 else 0))
  have hmem : a ∈ bad := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ha, by omega⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image bad (fun b => b p) ⟨a,hmem⟩
  have hbf : f b ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hb).1
  have hbb := (Finset.mem_filter.mp hb).2
  have hz : (generator q ^ 2 * f) (twice p+b) = 0 := by
    by_contra hn
    obtain ⟨c,hc,he⟩ := square_coeff_nonzero q f (twice p+b) hn
    have hep := congrFun he p
    simp only [Pi.add_apply, twice_apply, if_neg hpq.symm, ite_true, zero_add] at hep
    have hcb : c ∈ bad := by
      apply Finset.mem_filter.mpr
      refine ⟨Finsupp.mem_support_iff.mpr hc, ?_⟩
      rcases hk with rfl | ⟨hkp,hkq⟩
      · simp only [if_pos rfl] at hbb ⊢
        omega
      · have hek := congrFun he k
        simp only [Pi.add_apply, twice_apply, if_neg (Ne.symm hkp), if_neg hkq.symm,
          zero_add] at hek
        simpa only [hek] using hbb
    have hm : c p ≤ b p := hmax c hcb
    omega
  have hn : ((generator p ^ 2 - generator q ^ 2) * f) (twice p+b) ≠ 0 := by
    simpa only [sub_mul, Finsupp.sub_apply, square_coeff_same, hz, sub_zero] using hbf
  have hbnd := h _ hn
  simp only [Pi.add_apply, twice_apply] at hbnd
  by_cases hkp : k=p
  · subst k
    simp only [ite_true] at hbnd hbb
    omega
  · simp only [if_neg hkp, if_neg (Ne.symm hkp)] at hbnd hbb
    omega

theorem s_box {n : ℕ} (i : Fin (n+1)) (b : Fin (n+2) → ℕ)
    (f : SkewPolynomial (n+2)) (hf : f ∈ Box b) :
    s i f ∈ Box (b ∘ Equiv.swap i.castSucc i.succ) := by
  classical
  have he := (Finsupp.sum_single f).symm
  rw [he]
  simp only [Finsupp.sum, map_sum]
  apply (Box _).sum_mem
  intro a ha
  obtain ⟨c,_,hc⟩ := ElementaryGeneration.s_monomial i a (f a)
  rw [hc]
  apply monomial_mem_box
  intro j
  exact (mem_box _ _).mp hf a (Finsupp.mem_support_iff.mp ha) _

/-- Stability of the literal staircase box under every genuine odd divided difference. -/
theorem divided_mem_H {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (hf : f ∈ H (n+2)) : divided i f ∈ H (n+2) := by
  classical
  rw [H_eq_box] at hf ⊢
  let b : Fin (n+2) → ℕ := fun k => n+2-1-k.val
  let e : Fin (n+2) → ℕ := expSingle i.castSucc + expSingle i.succ
  let B : Fin (n+2) → ℕ := fun k =>
    if k=i.castSucc ∨ k=i.succ then n+2-i.val else b k
  have hi : i.castSucc ≠ i.succ := adjacent_ne i
  have hd : generator i.castSucc - generator i.succ ∈ Box e := by
    apply (Box e).sub_mem <;> apply monomial_mem_box <;> intro k <;>
      dsimp [e] <;> omega
  have h₁ : ∀ k, e k + b k ≤ B k := by
    intro k
    by_cases hl : k=i.castSucc
    · subst k; simp [e, expSingle, hi, hi.symm, B, b, Fin.val_succ]; omega
    · by_cases hr : k=i.succ
      · subst k; simp [e, expSingle, hi, hi.symm, B, b, Fin.val_succ]; omega
      · simp [e, expSingle, Ne.symm hl, Ne.symm hr, B, hl, hr]
  have h₂ : ∀ k, (b ∘ Equiv.swap i.castSucc i.succ) k + e k ≤ B k := by
    intro k
    by_cases hl : k=i.castSucc
    · subst k; simp [e, expSingle, hi, hi.symm, B, b, Fin.val_succ]; omega
    · by_cases hr : k=i.succ
      · subst k; simp [e, expSingle, hi, hi.symm, B, b, Fin.val_succ]; omega
      · simp [e, expSingle, Ne.symm hl, Ne.symm hr, B, hl, hr,
          Equiv.swap_apply_of_ne_of_ne hl hr]
  have hR : (generator i.castSucc ^ 2 - generator i.succ ^ 2) * divided i f ∈ Box B := by
    rw [ElementaryGeneration.divided_intertwiner]
    exact (Box B).sub_mem (box_mono h₁ (box_mul hd hf))
      (box_mono h₂ (box_mul (s_box i b f hf) hd))
  have hR' : (generator i.succ ^ 2 - generator i.castSucc ^ 2) * divided i f ∈ Box B := by
    rw [show generator i.succ ^ 2 - generator i.castSucc ^ 2 =
      -(generator i.castSucc ^ 2 - generator i.succ ^ 2) by abel, neg_mul]
    exact (Box B).neg_mem hR
  rw [mem_box]
  intro a ha k
  by_cases hl : k=i.castSucc
  · subst k
    have h := square_difference_bound i.castSucc i.succ i.castSucc hi (Or.inl rfl)
      (divided i f) (B i.castSucc) (fun a ha => (mem_box _ _).mp hR a ha _) a ha
    simp only [ite_true, B, true_or] at h
    change a i.castSucc ≤ n+2-1-i.val
    omega
  · by_cases hr : k=i.succ
    · subst k
      have h := square_difference_bound i.succ i.castSucc i.succ hi.symm (Or.inl rfl)
        (divided i f) (B i.succ) (fun a ha => (mem_box _ _).mp hR' a ha _) a ha
      simp only [ite_true, B, or_true] at h
      change a i.succ ≤ n+2-1-(i.val+1)
      omega
    · have h := square_difference_bound i.castSucc i.succ k hi (Or.inr ⟨hl,hr⟩)
        (divided i f) (B k) (fun a ha => (mem_box _ _).mp hR a ha _) a ha
      simpa only [if_neg hl, add_zero, B, hl, hr, false_or, ite_false, b] using h

theorem applyWord_mem_H {n : ℕ} (w : Word n) (f : SkewPolynomial (n+2))
    (hf : f ∈ H (n+2)) : LongestDivided.applyWord w f ∈ H (n+2) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact divided_mem_H i _ ih

/-- The first assertion of Lemma 2.12, for the inherited chosen-word convention. -/
theorem schubert_mem_H {n : ℕ} (w : Perm n) : schubert w ∈ H (n+2) := by
  unfold schubert
  rw [dividedElementOperator_eq]
  apply applyWord_mem_H
  exact Submodule.subset_span ⟨⟨fun i => n+2-1-i.val, fun _ => le_rfl⟩, rfl⟩

/-- The bounded exponent box has exactly N! indices, including the last zero. -/
def stairPiEquiv (N : ℕ) : StairIndex N ≃ ((i : Fin N) → Fin (N-i.val)) where
  toFun a i := ⟨a.val i, by have h := a.property i; have := i.isLt; omega⟩
  invFun a := ⟨fun i => (a i).val, fun i => by change (a i).val ≤ N-1-i.val; have h := (a i).isLt; have := i.isLt; omega⟩
  left_inv a := rfl
  right_inv a := rfl

theorem stair_card (N : ℕ) : Fintype.card (StairIndex N) = N.factorial := by
  classical
  rw [Fintype.card_congr (stairPiEquiv N), Fintype.card_pi]
  simp only [Fintype.card_fin]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_succ]
    simp [Nat.factorial_succ, Nat.succ_sub_succ_eq_sub, ih]

/-- Actual staircase coefficient coordinates. -/
def stairCoords (N : ℕ) : H N ≃ₗ[ℤ] (StairIndex N →₀ ℤ) :=
  (LinearEquiv.ofEq (H N) (Box (fun i => N-1-i.val)) (H_eq_box N)).trans
    (Finsupp.supportedEquivFinsupp (R := ℤ) (M := ℤ) {a : Fin N → ℕ | ∀ i, a i ≤ N-1-i.val})

/-- Constant term of the actual operator, with no replacement action. -/
def selector {n : ℕ} (w : Perm n) : SkewPolynomial (n+2) →ₗ[ℤ] ℤ :=
  (Finsupp.lapply 0).comp (dividedElementOperator w)

@[simp] theorem selector_apply {n : ℕ} (w : Perm n) (f : SkewPolynomial (n+2)) :
    selector w f = dividedElementOperator w f 0 := rfl

def diagonal {n : ℕ} (w : Perm n) : ℤ := selector w (schubert w)

theorem diagonal_square {n : ℕ} (w : Perm n) : diagonal w * diagonal w = 1 := by
  have hone : (1 : SkewPolynomial (n+2)) (0 : Fin (n+2) → ℕ) = 1 := Finsupp.single_eq_same
  rcases action_self w with h | h <;>
    simp [diagonal, selector_apply, h, hone]

theorem selector_shorter {n : ℕ} (w v : Perm n) (h : length v < length w) :
    selector w (schubert v) = 0 := by simp [action_shorter w v h]

theorem selector_distinct {n : ℕ} (w v : Perm n) (h : length v = length w) (hne : v ≠ w) :
    selector w (schubert v) = 0 := by simp [action_same_length_distinct w v h hne]

/-- Integral elimination, one whole length layer at a time; diagonal inverses are ±1. -/
theorem selector_solve {n : ℕ} (y : Perm n → ℤ) :
    ∃ f ∈ Submodule.span ℤ (Set.range (schubert (n := n))), ∀ w, selector w f = y w := by
  classical
  let S := Submodule.span ℤ (Set.range (schubert (n := n)))
  have claim : ∀ k, k ≤ (n+2).choose 2 + 1 →
      ∃ f ∈ S, ∀ w, k ≤ length w → selector w f = y w := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      refine ⟨0, S.zero_mem, ?_⟩
      intro w hw
      have := length_le_max w
      omega
    | of_succ k _ ih =>
      obtain ⟨f,hf,hsolve⟩ := ih
      let T := Finset.univ.filter (fun v : Perm n => length v = k)
      let c := fun v : Perm n => (y v - selector v f) * diagonal v
      let g := ∑ v ∈ T, c v • schubert v
      have hg : g ∈ S := S.sum_mem (fun v _ => S.smul_mem _ (Submodule.subset_span ⟨v,rfl⟩))
      refine ⟨f+g, S.add_mem hf hg, ?_⟩
      intro w hw
      rw [map_add]
      have he : selector w g = ∑ v ∈ T, c v * selector w (schubert v) := by
        simp only [g, map_sum, map_smul, smul_eq_mul]
      rw [he]
      by_cases hk : k = length w
      · rw [Finset.sum_eq_single w]
        · change selector w f + ((y w - selector w f) * diagonal w) * diagonal w = y w
          rw [mul_assoc, diagonal_square, mul_one]
          ring
        · intro v hv hne
          have hvk := (Finset.mem_filter.mp hv).2
          rw [selector_distinct w v (hvk.trans hk) hne, mul_zero]
        · intro hn
          exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.symm⟩)).elim
      · rw [Finset.sum_eq_zero]
        · simpa using hsolve w (by omega)
        · intro v hv
          have hvk := (Finset.mem_filter.mp hv).2
          rw [selector_shorter w v (by omega), mul_zero]
  obtain ⟨f,hf,he⟩ := claim 0 (Nat.zero_le _)
  exact ⟨f,hf,fun w => he w (Nat.zero_le _)⟩

def allSelectors (n : ℕ) : H (n+2) →ₗ[ℤ] (Perm n → ℤ) :=
  (LinearMap.pi (fun w => selector w)).comp (H (n+2)).subtype

theorem schubertSpan_le_H (n : ℕ) :
    Submodule.span ℤ (Set.range (schubert (n := n))) ≤ H (n+2) :=
  Submodule.span_le.mpr (by rintro _ ⟨w,rfl⟩; exact schubert_mem_H w)

theorem allSelectors_surjective (n : ℕ) : Function.Surjective (allSelectors n) := by
  intro y
  obtain ⟨f,hf,he⟩ := selector_solve y
  exact ⟨⟨f,schubertSpan_le_H n hf⟩, funext he⟩

/-- The cardinality is used only to give an independent lattice embedding;
the proved integral surjection, not rational rank, supplies unimodularity. -/
def cardinalCoords (n : ℕ) : H (n+2) ≃ₗ[ℤ] (Perm n → ℤ) :=
  ((stairCoords (n+2)).trans (Finsupp.domLCongr (Fintype.equivOfCardEq
    (show Fintype.card (StairIndex (n+2)) = Fintype.card (Perm n) by
      rw [stair_card, Fintype.card_perm, Fintype.card_fin])))).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Perm n))

theorem allSelectors_injective (n : ℕ) : Function.Injective (allSelectors n) :=
  IsNoetherian.injective_of_surjective_of_injective (cardinalCoords n).toLinearMap
    (allSelectors n) (cardinalCoords n).injective (allSelectors_surjective n)

/-- Integral spanning: no field extension and no assumed integral coordinates. -/
theorem H_eq_schubertSpan (n : ℕ) :
    H (n+2) = Submodule.span ℤ (Set.range (schubert (n := n))) := by
  apply le_antisymm _ (schubertSpan_le_H n)
  intro f hf
  obtain ⟨g,hg,he⟩ := selector_solve (fun w => selector w f)
  have hfg : (⟨g,schubertSpan_le_H n hg⟩ : H (n+2)) = ⟨f,hf⟩ :=
    allSelectors_injective n (funext he)
  have hgf : g=f := congrArg Subtype.val hfg
  exact hgf ▸ hg

/-- Lemma 2.12: an actual integral basis of the literal H. -/
def schubertBasis (n : ℕ) : Basis (Perm n) ℤ (H (n+2)) :=
  (Basis.span (schubert_linearIndependent n)).map
    (LinearEquiv.ofEq _ _ (H_eq_schubertSpan n).symm)

@[simp] theorem schubertBasis_val (n : ℕ) (w : Perm n) :
    (schubertBasis n w : SkewPolynomial (n+2)) = schubert w := by
  simp only [schubertBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]

/-- Universal unique integer expansion in the literal Schubert polynomials. -/
theorem integer_expansion_unique {n : ℕ} (f : SkewPolynomial (n+2)) (hf : f ∈ H (n+2)) :
    ∃! c : Perm n → ℤ, f = ∑ w, c w • schubert w := by
  classical
  let x : H (n+2) := ⟨f,hf⟩
  refine ⟨fun w => (schubertBasis n).repr x w, ?_, ?_⟩
  · have he := congrArg Subtype.val ((schubertBasis n).sum_repr x)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, schubertBasis_val] using he.symm
  · intro c hc
    have he : x = ∑ w, c w • schubertBasis n w := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, schubertBasis_val] using hc
    funext w
    simpa only [(schubertBasis n).repr_sum_self] using
      (congrArg (fun z => (schubertBasis n).repr z w) he).symm

def stairBasis (N : ℕ) : Basis (StairIndex N) ℤ (H N) :=
  Basis.span ((Finsupp.linearIndependent_single_one ℤ (Fin N → ℕ) :
    LinearIndependent ℤ (fun a : Fin N → ℕ => monomial a (1 : ℤ))).comp
      (fun a : StairIndex N => a.val) Subtype.val_injective)

@[simp] theorem stairBasis_val (N : ℕ) (a : StairIndex N) :
    (stairBasis N a : SkewPolynomial N) = stairMonomial a := Basis.span_apply _ _

/-- Scalar extension of a proved integral basis change. Used for both kernel sides. -/
def changeCoeffs {V M α β : Type*} [AddCommGroup V]
    [AddCommGroup M] [Fintype α] [Fintype β]
    (b : Basis α ℤ V) (d : Basis β ℤ V) (c : α → M) : β → M :=
  fun j => ∑ i, d.repr (b i) j • c i

theorem changeCoeffs_inverse {V M α β : Type*} [AddCommGroup V]
    [AddCommGroup M] [Fintype α] [Fintype β]
    (b : Basis α ℤ V) (d : Basis β ℤ V) (c : α → M) :
    changeCoeffs d b (changeCoeffs b d c) = c := by
  classical
  funext k
  dsimp only [changeCoeffs]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, b.sum_repr_mul_repr d]
  simp

abbrev K (n : ℕ) := OddSymmetricKernel.kernelSubring n

def toStair {n : ℕ} (c : Perm n → K n) : StairIndex (n+2) → K n :=
  changeCoeffs (schubertBasis n) (stairBasis (n+2)) c

def toSchubert {n : ℕ} (c : StairIndex (n+2) → K n) : Perm n → K n :=
  changeCoeffs (stairBasis (n+2)) (schubertBasis n) c

@[simp] theorem toSchubert_toStair {n : ℕ} (c : Perm n → K n) :
    toSchubert (toStair c) = c := changeCoeffs_inverse _ _ _

@[simp] theorem toStair_toSchubert {n : ℕ} (c : StairIndex (n+2) → K n) :
    toStair (toSchubert c) = c := changeCoeffs_inverse _ _ _

theorem schubert_stair_expansion {n : ℕ} (w : Perm n) :
    (∑ a, (stairBasis (n+2)).repr (schubertBasis n w) a • stairMonomial a) = schubert w := by
  have h := congrArg Subtype.val ((stairBasis (n+2)).sum_repr (schubertBasis n w))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, stairBasis_val, schubertBasis_val] using h

theorem right_change {n : ℕ} (c : Perm n → K n) :
    (∑ a, stairMonomial a * (toStair c a : SkewPolynomial (n+2))) =
      ∑ w, schubert w * (c w : SkewPolynomial (n+2)) := by
  classical
  dsimp only [toStair, changeCoeffs]
  simp only [ AddSubmonoidClass.coe_finset_sum, AddSubgroupClass.coe_zsmul, Finset.mul_sum,
    mul_smul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [← smul_mul_assoc, ← Finset.sum_mul, schubert_stair_expansion]

theorem left_change {n : ℕ} (c : Perm n → K n) :
    (∑ a, (toStair c a : SkewPolynomial (n+2)) * stairMonomial a) =
      ∑ w, (c w : SkewPolynomial (n+2)) * schubert w := by
  classical
  dsimp only [toStair, changeCoeffs]
  simp only [ AddSubmonoidClass.coe_finset_sum, AddSubgroupClass.coe_zsmul, Finset.sum_mul,
    smul_mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [← mul_smul_comm, ← Finset.mul_sum, schubert_stair_expansion]

/-- Proposition 2.13, RIGHT coefficients in the actual joint kernel, all polynomials. -/
theorem right_kernel_decomposition_unique (n : ℕ) (f : SkewPolynomial (n+2)) :
    ∃! c : Perm n → K n, f = ∑ w, schubert w * (c w : SkewPolynomial (n+2)) := by
  classical
  obtain ⟨d,hd,hu⟩ := StaircaseIndependence.right_kernel_decomposition_unique n f
  refine ⟨toSchubert d, ?_, ?_⟩
  · dsimp only
    rw [← right_change, toStair_toSchubert]
    exact hd
  · intro c hc
    have he : toStair c = d := hu (toStair c) (hc.trans (right_change c).symm)
    simpa using congrArg toSchubert he

/-- Proposition 2.13, LEFT coefficients, with multiplication order retained. -/
theorem left_kernel_decomposition_unique (n : ℕ) (f : SkewPolynomial (n+2)) :
    ∃! c : Perm n → K n, f = ∑ w, (c w : SkewPolynomial (n+2)) * schubert w := by
  classical
  obtain ⟨d,hd,hu⟩ := StaircaseLeft.left_kernel_decomposition_unique n f
  refine ⟨toSchubert d, ?_, ?_⟩
  · dsimp only
    rw [← left_change, toStair_toSchubert]
    exact hd
  · intro c hc
    have he : toStair c = d := hu (toStair c) (hc.trans (left_change c).symm)
    simpa using congrArg toSchubert he

end
end OddMath.Frontier.SchubertBasis
