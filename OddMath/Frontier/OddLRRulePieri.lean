import OddMath.Frontier.OddLRRuleFull
import OddMath.Frontier.EKLSectionTwoF

/-!
# Iterated right Pieri rule from a Schur function: skew signed Kostka numbers

For partitions `μ` and a sequence of positive integers `c₁, …, c_t`,
`s_μ h_{c₁} ⋯ h_{c_t} = Σ_λ (-1)^{N(μ)+N(λ)} (Σ_{S ∈ SSYT(λ/μ, c)} (-1)^{N^<(Ŝ)}) s_λ` in `OΛ`
(`skew_pieri`). This iterates the odd horizontal Pieri rule in `OΛ`
(`EKLSectionTwo.horizontal_pieri_Q`, EKL (2.72); Ellis, arXiv:1111.3932v1, Prop. 3.7 (3.8))
along the strips of `T_S` (E, proof of Theorem 4.8, p.14), with the sign bookkeeping of the proof
of E Theorem 3.8 (`CompleteTableauExpansion.neLess_extend`, `recording_sign`).
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauEvaluation TableauContent OddLRTableau CompleteTableauExpansion
open DegreeShapes TableauStripCorners
open EKRadicalQuotient (Q)
open OddLREKIdentification (sK)
open scoped BigOperators

/-! ## `h_k = s_{(k)}` in `OΛ` (E Lemma 3.5 (3.6)) -/

theorem row_eq_rowShape (k : ℕ) :
    (OddLRVerticalPieri.column k).transpose = TableauExtremal.rowShape k := by
  apply YoungDiagram.ext
  ext p
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, OddLRVerticalPieri.mem_column]
  change _ ↔ p ∈ ({0} ×ˢ Finset.range k : Finset (ℕ × ℕ))
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
  simp only [Prod.fst_swap, Prod.snd_swap]
  omega

theorem north_rowShape (k : ℕ) : TableauStripSigns.north (TableauExtremal.rowShape k) = 0 := by
  unfold TableauStripSigns.north
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  change p ∈ ({0} ×ˢ Finset.range k : Finset (ℕ × ℕ)) at hp
  change q ∈ ({0} ×ˢ Finset.range k : Finset (ℕ × ℕ)) at hq
  rw [Finset.mem_product, Finset.mem_singleton] at hp hq
  omega

theorem directNorth_rowShape (k : ℕ) :
    TableauStripSigns.directNorth (TableauExtremal.rowShape k) = 0 := by
  unfold TableauStripSigns.directNorth
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  change p ∈ ({0} ×ˢ Finset.range k : Finset (ℕ × ℕ)) at hp
  change q ∈ ({0} ×ˢ Finset.range k : Finset (ℕ × ℕ)) at hq
  rw [Finset.mem_product, Finset.mem_singleton] at hp hq
  omega

set_option synthInstance.maxHeartbeats 200000 in
/-- `h_k = s_{(k)}` in `OΛ`. -/
theorem h_eq_sK_row (k : ℕ) :
    EKElementaryQuotient.h k = sK (OddLRVerticalPieri.column k).transpose := by
  rw [← sub_eq_zero]
  apply EKLSectionTwo.eq_zero_of_piN
  intro N
  rw [map_sub, OddLREKIdentification.piN_h, OddLREKIdentification.piN_sK, row_eq_rowShape,
    CompleteTableauExpansion.sp, north_rowShape, directNorth_rowShape,
    TableauExtremal.tableauPolynomial_row, pow_zero, one_smul, sub_self]

/-! ## Fibers of tableaux restricting to `T_μ` -/

variable (mu : YoungDiagram) (c : ℕ → ℕ)

/-- Content of `T_S` for `S` of content `c₁, …, c_t`. -/
noncomputable def muContent (t : ℕ) : ℕ →₀ ℕ :=
  TableauDominance.shapeContent mu +
    ∑ i ∈ Finset.range t, Finsupp.single (mu.colLen 0 + i + 1) (c (i + 1))

/-- Tableaux of shape `λ` restricting to `T_μ`, with content `muContent`. -/
abbrev MF (t : ℕ) (lam : YoungDiagram) :=
  {T : PositiveTableau lam // FullCond mu T ∧ content T = muContent mu c t}

noncomputable instance (t : ℕ) (lam : YoungDiagram) : Fintype (MF mu c t lam) := by
  classical
  exact Set.Finite.fintype ((finite_content lam (muContent mu c t)).subset (fun T hT => hT.2))

/-- Degree of `muContent`. -/
def mdeg (t : ℕ) : ℕ := mu.card + prefixDegree c t

variable {mu c}

theorem muContent_succ (t : ℕ) :
    muContent mu c (t + 1) = muContent mu c t + Finsupp.single (mu.colLen 0 + t + 1) (c (t + 1)) := by
  simp [muContent, Finset.sum_range_succ, add_assoc]

theorem muContent_apply_gt (t : ℕ) {k : ℕ} (hk : mu.colLen 0 + t < k) : muContent mu c t k = 0 := by
  simp only [muContent, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_zero (fun i hi => by rw [if_neg (by have := Finset.mem_range.mp hi; omega)])]
  simp only [add_zero, TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have := row_lt_colLen (show (p.1, p.2) ∈ mu from by simpa using hp)
  rw [if_neg (by omega)]

theorem mf_bounded {t : ℕ} {lam : YoungDiagram} (T : MF mu c t lam) :
    InAlphabet (mu.colLen 0 + t) T.1 := by
  intro p hp
  have hm := entry_mem_support T.1 hp
  rw [T.2.2, Finsupp.mem_support_iff] at hm
  by_contra hn
  exact hm (muContent_apply_gt t (by omega))

theorem sum_muContent (t : ℕ) : (muContent mu c t).sum (fun _ n => n) = mdeg mu c t := by
  unfold muContent mdeg
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  congr 1
  · rw [← TableauDominance.content_canonical, content_total]
  · rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index (h := fun _ n : ℕ => n) rfl]
    rfl

theorem mf_card {t : ℕ} {lam : YoungDiagram} (T : MF mu c t lam) : lam.card = mdeg mu c t := by
  rw [← content_total T.1, T.2.2, sum_muContent]

/-! ## One Pieri step -/

variable (mu c)

abbrev MFStep (t : ℕ) (lam : YoungDiagram) :=
  Σ κ : {κ : DegreeShape (mdeg mu c t) // Horizontal κ.val lam}, MF mu c t κ.val.val

variable {mu c}

theorem fullCond_extend {kap lam : YoungDiagram} (T : PositiveTableau kap) (r : ℕ)
    (hb : InAlphabet r T) (hh : Horizontal kap lam) (hr : mu.colLen 0 ≤ r)
    (hT : FullCond mu T) : FullCond mu (extendTableau T r hb hh) := by
  refine ⟨le_trans hT.1 (YoungDiagram.cells_subset_iff.mp hh.1), fun i j h => ?_, fun i j h h' => ?_⟩
  · have hk : (i, j) ∈ kap.cells := by simpa using mem_of_le hT.1 h
    rw [show (extendTableau T r hb hh).entry i j = (extendTableau T r hb hh).entry (i, j).1 (i, j).2
      from rfl, extend_old T r hb hh hk]
    exact hT.2.1 i j h
  · by_cases hk : (i, j) ∈ kap.cells
    · rw [show (extendTableau T r hb hh).entry i j = (extendTableau T r hb hh).entry (i, j).1 (i, j).2
        from rfl, extend_old T r hb hh hk]
      exact hT.2.2 i j (by simpa using hk) h'
    · rw [show (extendTableau T r hb hh).entry i j = (extendTableau T r hb hh).entry (i, j).1 (i, j).2
        from rfl, extend_new T r hb hh (Finset.mem_sdiff.mpr ⟨by simpa using h, hk⟩)]
      omega

theorem fullCond_prefix {lam : YoungDiagram} (T : PositiveTableau lam) (r : ℕ)
    (hr : mu.colLen 0 ≤ r) (hT : FullCond mu T) : FullCond mu (prefixTableau T r) := by
  have hsub : ∀ i j, (i, j) ∈ mu → (i, j) ∈ (prefixShape T r).cells := by
    intro i j h
    rw [mem_prefix]
    refine ⟨by simpa using mem_of_le hT.1 h, ?_⟩
    rw [hT.2.1 i j h]; have := row_lt_colLen h; omega
  refine ⟨YoungDiagram.cells_subset_iff.mp (fun p hp => hsub p.1 p.2 (by simpa using hp)),
    fun i j h => ?_, fun i j h h' => ?_⟩
  · rw [show (prefixTableau T r).entry i j = (prefixTableau T r).entry (i, j).1 (i, j).2 from rfl,
      prefix_entry T r (hsub i j h)]
    exact hT.2.1 i j h
  · have hp : (i, j) ∈ (prefixShape T r).cells := by simpa using h
    rw [show (prefixTableau T r).entry i j = (prefixTableau T r).entry (i, j).1 (i, j).2 from rfl,
      prefix_entry T r hp]
    exact hT.2.2 i j (by simpa using (mem_prefix T r _).mp hp |>.1) h'

theorem step_card' (t : ℕ) (u : DegreeShape (mdeg mu c t)) (v : DegreeShape (mdeg mu c (t + 1)))
    (hh : Horizontal u.val v.val) : (v.val.cells \ u.val.cells).card = c (t + 1) := by
  rw [Finset.card_sdiff hh.1]
  change v.val.card - u.val.card = _
  rw [u.property, v.property, mdeg, mdeg, prefixDegree_succ]
  omega

def mfStepMap (t : ℕ) (v : DegreeShape (mdeg mu c (t + 1))) (x : MFStep mu c t v.val) :
    MF mu c (t + 1) v.val :=
  ⟨extendTableau x.2.val (mu.colLen 0 + t) (mf_bounded x.2) x.1.property,
    fullCond_extend _ _ _ _ (by omega) x.2.2.1, by
    rw [extend_content, x.2.2.2, step_card' t x.1.val v x.1.property, muContent_succ]⟩

theorem mf_prefix_content (t : ℕ) {lam : YoungDiagram} (T : MF mu c (t + 1) lam) :
    content (prefixTableau T.val (mu.colLen 0 + t)) = muContent mu c t := by
  ext k
  rw [prefix_content_apply, T.2.2, muContent_succ, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hk : k ≤ mu.colLen 0 + t
  · rw [if_pos hk, if_neg (by omega), Nat.add_zero]
  · rw [if_neg hk, muContent_apply_gt t (by omega)]

theorem mfStepMap_bijective (t : ℕ) (v : DegreeShape (mdeg mu c (t + 1))) :
    Function.Bijective (mfStepMap t v) := by
  constructor
  · rintro ⟨⟨⟨κ, hd⟩, hm⟩, T, hT⟩ ⟨⟨⟨κ', hd'⟩, hm'⟩, T', hT'⟩ he
    have ht := congrArg Subtype.val he
    change extendTableau T _ (mf_bounded ⟨T, hT⟩) hm =
      extendTableau T' _ (mf_bounded ⟨T', hT'⟩) hm' at ht
    have hs := congrArg (fun S => prefixShape S (mu.colLen 0 + t)) ht
    dsimp only at hs
    rw [prefix_extend_shape, prefix_extend_shape] at hs
    subst κ'
    have ht' : T = T' := by
      apply ext_cells
      intro p hp
      have hh := congrArg (fun S : PositiveTableau v.val => S.entry p.1 p.2) ht
      simpa only [extend_old _ _ _ _ hp] using hh
    subst T'
    rfl
  · intro T
    have hb := mf_bounded T
    have hpc := mf_prefix_content t T
    refine ⟨⟨⟨⟨prefixShape T.val (mu.colLen 0 + t), ?_⟩,
      prefix_horizontal T.val _ (by simpa [Nat.add_assoc] using hb)⟩,
      ⟨prefixTableau T.val _, fullCond_prefix _ _ (by omega) T.2.1, hpc⟩⟩, ?_⟩
    · rw [← content_total (prefixTableau T.val _), hpc, sum_muContent]
    · apply Subtype.ext
      exact extend_prefix T.val _ (by simpa [Nat.add_assoc] using hb)

noncomputable def mfStepEquiv (t : ℕ) (v : DegreeShape (mdeg mu c (t + 1))) :
    MFStep mu c t v.val ≃ MF mu c (t + 1) v.val :=
  Equiv.ofBijective _ (mfStepMap_bijective t v)

/-! ## The recursion for the signed fiber sums -/

attribute [local instance] degreeFintype Classical.propDecidable
open TableauHorizontalPieri (stripCount)

variable (mu c) in
/-- `Σ_{T} (-1)^{NE^<(T)}` over tableaux of shape `λ` restricting to `T_μ` with content `c`. -/
noncomputable def W (t : ℕ) (lam : YoungDiagram) : ℤ := ∑ T : MF mu c t lam, (-1 : ℤ) ^ neLess T.1

theorem W_succ (t : ℕ) (v : DegreeShape (mdeg mu c (t + 1))) :
    W mu c (t + 1) v.val = ∑ u : DegreeShape (mdeg mu c t),
      if Horizontal u.val v.val then W mu c t u.val * (-1 : ℤ) ^ stripCount u.val v.val else 0 := by
  unfold W
  rw [← (mfStepEquiv t v).sum_comp (fun T => (-1 : ℤ) ^ neLess T.val)]
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ u : {u : DegreeShape (mdeg mu c t) // Horizontal u.val v.val},
        (∑ T : MF mu c t u.val.val, (-1 : ℤ) ^ neLess T.val) *
          (-1 : ℤ) ^ stripCount u.val.val v.val := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      change (-1 : ℤ) ^ neLess (extendTableau T.val _ (mf_bounded T) u.property) = _
      rw [neLess_extend, pow_add]
    _ = ∑ u ∈ Finset.univ.filter (fun u : DegreeShape (mdeg mu c t) => Horizontal u.val v.val),
        (∑ T : MF mu c t u.val, (-1 : ℤ) ^ neLess T.val) * (-1 : ℤ) ^ stripCount u.val v.val :=
      (Finset.sum_subtype (p := fun u : DegreeShape (mdeg mu c t) => Horizontal u.val v.val)
        (Finset.univ.filter (fun u => Horizontal u.val v.val)) (by simp)
        (fun u => (∑ T : MF mu c t u.val, (-1 : ℤ) ^ neLess T.val) *
          (-1 : ℤ) ^ stripCount u.val v.val)).symm
    _ = _ := by rw [Finset.sum_filter]

theorem neLess_canonical (mu : YoungDiagram) :
    neLess (TableauDominance.canonicalTableau mu) = TableauStripSigns.northEast mu := by
  unfold neLess TableauStripSigns.northEast
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.filter_congr
  intro q hq
  rw [TableauDominance.canonical_entry hq, TableauDominance.canonical_entry hp]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩

theorem shapeContent_apply_gt (mu : YoungDiagram) {k : ℕ} (hk : mu.colLen 0 < k) :
    TableauDominance.shapeContent mu k = 0 := by
  simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have := row_lt_colLen (show (p.1, p.2) ∈ mu from by simpa using hp)
  rw [if_neg (by omega)]

theorem W_zero (lam : YoungDiagram) :
    W mu c 0 lam = if lam = mu then (-1 : ℤ) ^ TableauStripSigns.northEast mu else 0 := by
  have hc0 : muContent mu c 0 = TableauDominance.shapeContent mu := by simp [muContent]
  have hshape : ∀ T : MF mu c 0 lam, lam = mu := by
    intro T
    apply le_antisymm _ T.2.1.1
    intro p hp
    by_contra hm
    have h1 := T.2.1.2.2 p.1 p.2 hp hm
    have hct : content T.1 = TableauDominance.shapeContent mu := T.2.2.trans hc0
    have h2 := entry_mem_support T.1 (show (p.1, p.2) ∈ lam.cells by simpa using hp)
    rw [hct, Finsupp.mem_support_iff] at h2
    exact h2 (shapeContent_apply_gt mu h1)
  by_cases hl : lam = mu
  · subst hl
    rw [if_pos rfl]
    have hcan : ∀ T : MF lam c 0 lam, T.1 = TableauDominance.canonicalTableau lam := by
      intro T
      apply ext_cells
      intro p hp
      rw [TableauDominance.canonical_entry hp]
      exact T.2.1.2.1 p.1 p.2 (by simpa using hp)
    have hmem : FullCond lam (TableauDominance.canonicalTableau lam) ∧
        content (TableauDominance.canonicalTableau lam) = muContent lam c 0 := by
      refine ⟨⟨le_rfl, fun i j h => ?_, fun i j h h' => absurd h h'⟩, ?_⟩
      · exact TableauDominance.canonical_entry (p := (i, j)) (by simpa using h)
      · rw [TableauDominance.content_canonical, hc0]
    letI : Unique (MF lam c 0 lam) :=
      { default := ⟨_, hmem⟩
        uniq := fun T => Subtype.ext (hcan T) }
    rw [W, Fintype.sum_unique]
    change (-1 : ℤ) ^ neLess (TableauDominance.canonicalTableau lam) = _
    rw [neLess_canonical]
  · rw [if_neg hl, W]
    haveI : IsEmpty (MF mu c 0 lam) := ⟨fun T => hl (hshape T)⟩
    exact Finset.sum_of_isEmpty _

theorem ell_eq_northEast' (lam : YoungDiagram) :
    EKSemiorthogonality.ell lam = TableauStripSigns.northEast lam := by
  classical
  unfold EKSemiorthogonality.ell TableauStripSigns.northEast
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem sum_degreeShape_congr {M : Type*} [AddCommMonoid M] {d d' : ℕ} (h : d = d')
    (f : YoungDiagram → M) :
    ∑ x : DegreeShape d, f x.val = ∑ x : DegreeShape d', f x.val := by
  subst h; rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The odd horizontal Pieri rule of `OΛ`, solved for `s_α h_k`. -/
theorem pieri_Q (α : YoungDiagram) (k d : ℕ) (hd : α.card + k = d) :
    sK α * EKElementaryQuotient.h k = ∑ w : DegreeShape d,
      if Horizontal α w.val then
        ((-1 : ℤ) ^ (TableauStripSigns.northEast α + TableauStripSigns.northEast w.val) *
          (-1 : ℤ) ^ stripCount α w.val) • sK w.val else 0 := by
  subst hd
  have h := EKLSectionTwo.horizontal_pieri_Q α k
  rw [h_eq_sK_row]
  have h2 := congrArg (fun y : Q => (-1 : ℤ) ^ EKSemiorthogonality.ell α • y) h
  simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul] at h2
  rw [h2, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [smul_smul, ell_eq_northEast', ell_eq_northEast']
    change _ = ((-1 : ℤ) ^ (TableauStripSigns.northEast α + TableauStripSigns.northEast w.val) *
      (-1 : ℤ) ^ EKLSectionTwo.stripRight α w.val) • sK w.val
    congr 1
    rw [pow_add]
    ring
  · rw [smul_zero]

/-- Iterated right Pieri rule, in terms of the fiber sums `W`. -/
theorem pieri_iter (t : ℕ) :
    sK mu * ((List.range t).map (fun i => EKElementaryQuotient.h (c (i + 1)))).prod =
      ∑ lam : DegreeShape (mdeg mu c t),
        ((-1 : ℤ) ^ TableauStripSigns.northEast lam.val * W mu c t lam.val) • sK lam.val := by
  induction t with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    have hd : mdeg mu c 0 = mu.card := by simp [mdeg, prefixDegree]
    symm
    rw [Fintype.sum_eq_single (α := DegreeShape (mdeg mu c 0)) ⟨mu, hd.symm⟩ ?_]
    · rw [W_zero, if_pos rfl, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    · intro b hb
      rw [W_zero, if_neg (fun h => hb (Subtype.ext h)), mul_zero, zero_smul]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      ← mul_assoc, ih, Finset.sum_mul]
    simp_rw [smul_mul_assoc]
    have hstep : ∀ u : DegreeShape (mdeg mu c t),
        sK u.val * EKElementaryQuotient.h (c (t + 1)) = ∑ w : DegreeShape (mdeg mu c (t + 1)),
          if Horizontal u.val w.val then
            ((-1 : ℤ) ^ (TableauStripSigns.northEast u.val + TableauStripSigns.northEast w.val) *
              (-1 : ℤ) ^ stripCount u.val w.val) • sK w.val else 0 := fun u =>
      pieri_Q u.val (c (t + 1)) _ (by rw [u.property, mdeg, mdeg, prefixDegree_succ]; ring)
    simp_rw [hstep, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [W_succ, Finset.mul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs
    · rw [smul_smul]
      congr 1
      rw [pow_add]
      ring_nf
      rw [show ((-1 : ℤ) ^ (TableauStripSigns.northEast u.val * 2)) = 1 by
        rw [pow_mul', neg_one_sq, one_pow]]
      ring
    · rw [smul_zero, mul_zero, zero_smul]

/-! ## From fibers of `T_S` to skew tableaux -/

theorem content_toFull_apply {lam : YoungDiagram} (S : SkewTableau lam mu) (k : ℕ) :
    content (toFull S) k = if k ≤ mu.colLen 0 then TableauDominance.shapeContent mu k
      else S.content (k - mu.colLen 0) := by
  have hsplit : lam.cells = mu.cells ∪ skewCells lam mu := by
    ext p
    simp only [Finset.mem_union, mem_skewCells, YoungDiagram.mem_cells]
    constructor
    · intro hp; by_cases hm : p ∈ mu
      · exact Or.inl hm
      · exact Or.inr ⟨hp, hm⟩
    · rintro (hm | ⟨hp, _⟩)
      · exact mem_of_le S.sub hm
      · exact hp
  have hdisj : Disjoint mu.cells (skewCells lam mu) := by
    rw [Finset.disjoint_left]
    intro p hm hs
    exact (mem_skewCells.mp hs).2 (by simpa using hm)
  rw [content_apply, hsplit, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj)]
  have hmu : ∀ p ∈ mu.cells, (toFull S).entry p.1 p.2 = p.1 + 1 := fun p hp =>
    toFull_entry_mu S (by simpa using hp)
  have hsk : ∀ p ∈ skewCells lam mu, (toFull S).entry p.1 p.2 = S.entry p.1 p.2 + mu.colLen 0 :=
    fun p hp => toFull_entry_skew S (mem_skewCells.mp hp).1 (mem_skewCells.mp hp).2
  have hshape : TableauDominance.shapeContent mu k = (mu.cells.filter (fun p => p.1 + 1 = k)).card := by
    simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply,
      Finset.card_filter]
  split_ifs with hk
  · have e : (skewCells lam mu).filter (fun p => (toFull S).entry p.1 p.2 = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      rw [hsk p hp]
      have := S.positive (mem_skewCells.mp hp).1 (mem_skewCells.mp hp).2
      omega
    rw [hshape, Finset.filter_congr (fun p hp => by rw [hmu p hp]), e, Finset.card_empty, add_zero]
  · have e : mu.cells.filter (fun p => (toFull S).entry p.1 p.2 = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      rw [hmu p hp]
      have := row_lt_colLen (show (p.1, p.2) ∈ mu from by simpa using hp)
      omega
    rw [e, Finset.card_empty, zero_add, S.content_apply]
    congr 1
    apply Finset.filter_congr
    intro p hp
    rw [hsk p hp]
    omega

theorem muContent_apply (t k : ℕ) :
    muContent mu c t k = if k ≤ mu.colLen 0 then TableauDominance.shapeContent mu k
      else prefixContent c t (k - mu.colLen 0) := by
  simp only [muContent, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  split_ifs with hk
  · rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega)]), add_zero]
  · rw [shapeContent_apply_gt mu (by omega), zero_add]
    obtain ⟨j, rfl⟩ : ∃ j, k = mu.colLen 0 + j + 1 := ⟨k - mu.colLen 0 - 1, by omega⟩
    rw [show mu.colLen 0 + j + 1 - mu.colLen 0 = j + 1 by omega, prefixContent_apply_succ]
    by_cases hj : j < t
    · rw [if_pos hj, Finset.sum_eq_single j]
      · rw [if_pos rfl]
      · intro i _ hi; rw [if_neg (by omega)]
      · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'
    · rw [if_neg hj]
      exact Finset.sum_eq_zero (fun i hi => by
        rw [if_neg (by have := Finset.mem_range.mp hi; omega)])

theorem content_toFull_iff {lam : YoungDiagram} (S : SkewTableau lam mu) (t : ℕ) :
    content (toFull S) = muContent mu c t ↔ S.content = prefixContent c t := by
  constructor
  · intro h
    ext j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [prefixContent_zero_apply, S.content_apply]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      exact (S.positive (mem_skewCells.mp hp).1 (mem_skewCells.mp hp).2).ne'
    · have := congrArg (fun f => f (j + mu.colLen 0)) h
      simp only [content_toFull_apply, muContent_apply, if_neg (show ¬ j + mu.colLen 0 ≤ mu.colLen 0
        by omega), Nat.add_sub_cancel] at this
      exact this
  · intro h
    ext k
    rw [content_toFull_apply, muContent_apply, h]

/-- Fibers of `T_S` are fibers of skew tableaux. -/
noncomputable def mfEquiv (t : ℕ) (lam : YoungDiagram) :
    MF mu c t lam ≃ {S : SkewTableau lam mu // S.content = prefixContent c t} where
  toFun T := ⟨fromFull T.1 T.2.1, by
    rw [← content_toFull_iff, toFull_fromFull]; exact T.2.2⟩
  invFun S := ⟨toFull S.1, fullCond_toFull S.1, (content_toFull_iff S.1 t).mpr S.2⟩
  left_inv T := Subtype.ext (toFull_fromFull T.1 T.2.1)
  right_inv S := Subtype.ext (fromFull_toFull S.1)

theorem W_eq (t : ℕ) (lam : YoungDiagram) :
    (-1 : ℤ) ^ TableauStripSigns.northEast lam * W mu c t lam =
      (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
        ∑ S ∈ ofContent lam mu (prefixContent c t), S.sign := by
  unfold W
  rw [← (mfEquiv t lam).symm.sum_comp, Finset.mul_sum, Finset.mul_sum]
  unfold ofContent
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  change (-1 : ℤ) ^ TableauStripSigns.northEast lam * (-1 : ℤ) ^ neLess (toFull S.1) = _
  rw [← pow_add, recording_sign, tableauSign_toFull]
  simp only [Function.Embedding.coe_subtype]
  rw [pow_add]
  ring

/-- **Skew Pieri expansion**: `s_μ h_{c₁} ⋯ h_{c_t} = Σ_λ (-1)^{N(μ)+N(λ)}
(Σ_{S ∈ SSYT(λ/μ, c)} (-1)^{N^<(Ŝ)}) s_λ` in `OΛ`. -/
theorem skew_pieri (t : ℕ) :
    sK mu * ((List.range t).map (fun i => EKElementaryQuotient.h (c (i + 1)))).prod =
      ∑ lam : DegreeShape (mdeg mu c t),
        ((-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam.val) *
          ∑ S ∈ ofContent lam.val mu (prefixContent c t), S.sign) • sK lam.val := by
  rw [pieri_iter]
  apply Finset.sum_congr rfl
  intro lam _
  rw [W_eq]

end OddMath.Frontier.OddLRRule
