import OddMath.Frontier.TableauHorizontalPieri
import OddMath.Frontier.OddSymmetricKernel
import OddMath.Frontier.KostkaModuleInversion

/-!
Ellis 1111.3932v1 Theorem 3.8: complete products and recording tableaux.
The proof constructs recording tableaux and their sign recurrence, then consumes
the inherited signed Kostka inverse for unconditional kernel membership.
-/
namespace OddMath.Frontier.CompleteTableauExpansion
open scoped BigOperators
open OddMath.SkewPolynomial
attribute [local instance] Classical.propDecidable
open TableauPolynomial TableauStripSigns TableauHorizontalPieri
open TableauStripCorners DegreeShapes TableauDominance FiniteCompleteElementary
noncomputable section

/-- Increasing row order, with the genuine finite row-length list. -/
def H (n : ℕ) (μ : YoungDiagram) : SkewPolynomial n :=
  (μ.rowLens.map (completePoly n)).prod

/-- The source normalization (3.4). -/
def sp (n : ℕ) (lam : YoungDiagram) : SkewPolynomial n :=
  (-1 : ℤ) ^ (directNorth lam + north lam) • tableauPolynomial n lam

/-! Recording tableaux: the sublevel shapes are genuine Young diagrams,
and each new label is a horizontal strip. These discharge the combinatorial
bijection premise in Theorem 3.8, rather than assuming a recording object. -/
open TableauSign TableauContent TableauEvaluation

variable {mu nu : YoungDiagram}

theorem entry_mono (T : PositiveTableau nu) {p q : ℕ × ℕ}
    (hp : p ∈ nu.cells) (hq : q ≤ p) : T.entry q.1 q.2 ≤ T.entry p.1 p.2 := by
  have hm := nu.up_left_mem hq.1 le_rfl hp
  have hr := T.toSemistandardYoungTableau.row_weak_of_le hq.2 hm
  rcases hq.1.eq_or_lt with he | he
  · simpa only [he] using hr
  · exact hr.trans (T.col_strict' he hp).le

/-- The actual cells carrying labels at most r, not an arbitrary shape chain. -/
def prefixShape (T : PositiveTableau nu) (r : ℕ) : YoungDiagram where
  cells := nu.cells.filter (fun p => T.entry p.1 p.2 ≤ r)
  isLowerSet := by
    intro p q hqp hp
    obtain ⟨hp, ht⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨nu.isLowerSet hqp hp, (entry_mono T hp hqp).trans ht⟩

@[simp] theorem mem_prefix (T : PositiveTableau nu) (r : ℕ) (p : ℕ × ℕ) :
    p ∈ (prefixShape T r).cells ↔ p ∈ nu.cells ∧ T.entry p.1 p.2 ≤ r :=
  Finset.mem_filter

/-- Restriction retains old entries and the required off-shape zeros. -/
def prefixTableau (T : PositiveTableau nu) (r : ℕ) : PositiveTableau (prefixShape T r) where
  entry i j := if (i,j) ∈ prefixShape T r then T.entry i j else 0
  row_weak' hj hp := by
    rw [if_pos hp, if_pos ((prefixShape T r).up_left_mem le_rfl hj.le hp)]
    exact T.row_weak' hj (Finset.mem_filter.mp hp).1
  col_strict' hi hp := by
    rw [if_pos hp, if_pos ((prefixShape T r).up_left_mem hi.le le_rfl hp)]
    exact T.col_strict' hi (Finset.mem_filter.mp hp).1
  zeros' hp := if_neg hp
  positive hp := by
    rw [if_pos hp]
    exact T.positive (Finset.mem_filter.mp hp).1

@[simp] theorem prefix_entry (T : PositiveTableau nu) (r : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ (prefixShape T r).cells) : (prefixTableau T r).entry p.1 p.2 = T.entry p.1 p.2 :=
  if_pos hp

theorem prefix_bounded (T : PositiveTableau nu) (r : ℕ) : InAlphabet r (prefixTableau T r) := by
  intro p hp
  rw [prefix_entry T r hp]
  exact (mem_prefix T r p).mp hp |>.2

theorem prefix_horizontal (T : PositiveTableau nu) (r : ℕ) (hb : InAlphabet (r+1) T) :
    Horizontal (prefixShape T r) nu := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro p hp q hq hc
  obtain ⟨hp, hpn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hq, hqn⟩ := Finset.mem_sdiff.mp hq
  have hpv : T.entry p.1 p.2 = r+1 := by
    have := hb p hp
    have hh : ¬ T.entry p.1 p.2 ≤ r := fun hh => hpn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    omega
  have hqv : T.entry q.1 q.2 = r+1 := by
    have := hb q hq
    have hh : ¬ T.entry q.1 q.2 ≤ r := fun hh => hqn (Finset.mem_filter.mpr ⟨hq,hh⟩)
    omega
  apply Prod.ext _ hc
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · have hh := T.col_strict' h hq
    have hx : T.entry p.1 q.2 = r+1 := by rw [← hc]; exact hpv
    omega
  · exact h
  · have hh := T.col_strict' h hp
    have hx : T.entry q.1 p.2 = r+1 := by rw [hc]; exact hqv
    omega

/-- Add exactly the horizontal skew cells, filling each by the next label. -/
def extendTableau (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) : PositiveTableau nu where
  entry i j := if (i,j) ∈ mu then T.entry i j else if (i,j) ∈ nu then r+1 else 0
  row_weak' := by
    intro i a b hab hp
    by_cases hm : (i,b) ∈ mu
    · rw [if_pos hm, if_pos (mu.up_left_mem le_rfl hab.le hm)]
      exact T.row_weak' hab hm
    · rw [if_neg hm, if_pos hp]
      split_ifs with ha
      · exact (hb (i,a) ha).trans (Nat.le_succ r)
      · omega
      · omega
  col_strict' := by
    intro a b j hab hp
    by_cases hm : (b,j) ∈ mu
    · rw [if_pos hm, if_pos (mu.up_left_mem hab.le le_rfl hm)]
      exact T.col_strict' hab hm
    · have ha : (a,j) ∈ mu := by
        by_contra hn
        have eq := hh.2 (a,j) (Finset.mem_sdiff.mpr ⟨nu.up_left_mem hab.le le_rfl hp,hn⟩)
          (b,j) (Finset.mem_sdiff.mpr ⟨hp,hm⟩) rfl
        have := congrArg Prod.fst eq
        omega
      rw [if_pos ha, if_neg hm, if_pos hp]
      exact Nat.lt_succ_of_le (hb (a,j) ha)
  zeros' := by
    intro i j hp
    have hn : (i,j) ∉ mu := fun hm => hp (hh.1 hm)
    rw [if_neg hn, if_neg hp]
  positive := by
    intro i j hp
    by_cases hm : (i,j) ∈ mu
    · rw [if_pos hm]; exact T.positive hm
    · rw [if_neg hm, if_pos hp]; omega

@[simp] theorem extend_old (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) {p : ℕ × ℕ} (hp : p ∈ mu.cells) :
    (extendTableau T r hb hh).entry p.1 p.2 = T.entry p.1 p.2 := if_pos hp

@[simp] theorem extend_new (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) {p : ℕ × ℕ} (hp : p ∈ nu.cells \ mu.cells) :
    (extendTableau T r hb hh).entry p.1 p.2 = r+1 := by
  rcases p with ⟨i,j⟩
  have hn : (i,j) ∉ mu := (Finset.mem_sdiff.mp hp).2
  have hm : (i,j) ∈ nu := (Finset.mem_sdiff.mp hp).1
  simp only [extendTableau, if_neg hn, if_pos hm]

theorem extend_bounded (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) : InAlphabet (r+1) (extendTableau T r hb hh) := by
  intro p hp
  by_cases hm : p ∈ mu.cells
  · rw [extend_old T r hb hh hm]; exact (hb p hm).trans (Nat.le_succ r)
  · rw [extend_new T r hb hh (Finset.mem_sdiff.mpr ⟨hp,hm⟩)]

/-- Exact content recurrence, including zero-sized steps and repeated letters. -/
theorem extend_content (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) :
    content (extendTableau T r hb hh) = content T + Finsupp.single (r+1) (nu.cells \ mu.cells).card := by
  unfold content
  rw [← Finset.sum_sdiff hh.1, add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro p hp
    rw [extend_old T r hb hh hp]
  · calc
      _ = ∑ _p ∈ nu.cells \ mu.cells, Finsupp.single (r+1) 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [extend_new T r hb hh hp]
      _ = _ := by simp [← Finsupp.single_smul]

theorem prefix_extend_shape (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) : prefixShape (extendTableau T r hb hh) r = mu := by
  apply YoungDiagram.ext
  ext p
  rw [mem_prefix]
  constructor
  · rintro ⟨hp,he⟩
    by_contra hn
    rw [extend_new T r hb hh (Finset.mem_sdiff.mpr ⟨hp,hn⟩)] at he
    omega
  · intro hp
    exact ⟨hh.1 hp, by rw [extend_old T r hb hh hp]; exact hb p hp⟩

theorem extend_prefix (T : PositiveTableau nu) (r : ℕ) (hb : InAlphabet (r+1) T) :
    extendTableau (prefixTableau T r) r (prefix_bounded T r) (prefix_horizontal T r hb) = T := by
  apply ext_cells
  intro p hp
  by_cases hm : p ∈ (prefixShape T r).cells
  · rw [extend_old _ _ _ _ hm, prefix_entry T r hm]
  · rw [extend_new _ _ _ _ (Finset.mem_sdiff.mpr ⟨hp,hm⟩)]
    have hh := hb p hp
    have hn : ¬ T.entry p.1 p.2 ≤ r := fun he => hm (Finset.mem_filter.mpr ⟨hp,he⟩)
    omega

abbrev RecordingStep (r : ℕ) (nu : YoungDiagram) :=
  Σ mu : {mu : YoungDiagram // Horizontal mu nu}, Tab r mu.val

def recordingStepMap (r : ℕ) (nu : YoungDiagram) (x : RecordingStep r nu) : Tab (r+1) nu :=
  ⟨extendTableau x.2.val r x.2.property x.1.property,
    extend_bounded x.2.val r x.2.property x.1.property⟩

theorem recordingStepMap_bijective (r : ℕ) (nu : YoungDiagram) :
    Function.Bijective (recordingStepMap r nu) := by
  constructor
  · rintro ⟨⟨mu,hm⟩,T,hT⟩ ⟨⟨mu',hm'⟩,T',hT'⟩ he
    have ht := congrArg Subtype.val he
    change extendTableau T r hT hm = extendTableau T' r hT' hm' at ht
    have hs := congrArg (fun S => prefixShape S r) ht
    dsimp only at hs
    rw [prefix_extend_shape, prefix_extend_shape] at hs
    subst mu'
    have ht' : T = T' := by
      apply ext_cells
      intro p hp
      have hh := congrArg (fun S : PositiveTableau nu => S.entry p.1 p.2) ht
      simpa only [extend_old T r hT hm hp, extend_old T' r hT' hm' hp] using hh
    subst T'
    rfl
  · rintro ⟨T,hT⟩
    refine ⟨⟨⟨prefixShape T r,prefix_horizontal T r hT⟩,
      ⟨prefixTableau T r,prefix_bounded T r⟩⟩, ?_⟩
    apply Subtype.ext
    exact extend_prefix T r hT

/-- Full-state one-step recording equivalence, with both round trips proved. -/
def recordingStepEquiv (r : ℕ) (nu : YoungDiagram) : RecordingStep r nu ≃ Tab (r+1) nu :=
  Equiv.ofBijective _ (recordingStepMap_bijective r nu)

/-- Content of the first r factor labels; zeros are allowed. -/
def prefixContent (c : ℕ → ℕ) (r : ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ Finset.range r, Finsupp.single (i+1) (c (i+1))

def prefixDegree (c : ℕ → ℕ) (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, c (i+1)

@[simp] theorem prefixContent_succ (c : ℕ → ℕ) (r : ℕ) :
    prefixContent c (r+1) = prefixContent c r + Finsupp.single (r+1) (c (r+1)) := by
  exact Finset.sum_range_succ _ _

@[simp] theorem prefixDegree_succ (c : ℕ → ℕ) (r : ℕ) :
    prefixDegree c (r+1) = prefixDegree c r + c (r+1) := Finset.sum_range_succ _ _

theorem prefixContent_above (c : ℕ → ℕ) {r k : ℕ} (hk : r < k) : prefixContent c r k = 0 := by
  unfold prefixContent
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (by have := Finset.mem_range.mp hi; omega)]

theorem prefixContent_total (c : ℕ → ℕ) (r : ℕ) :
    (prefixContent c r).sum (fun _ k => k) = prefixDegree c r := by
  unfold prefixContent prefixDegree
  rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index (h := fun _ k : ℕ => k) rfl]

abbrev Fiber (c : ℕ → ℕ) (r : ℕ) (nu : YoungDiagram) :=
  {T : PositiveTableau nu // content T = prefixContent c r}

instance fiberFinite (c : ℕ → ℕ) (r : ℕ) (nu : YoungDiagram) : Fintype (Fiber c r nu) :=
  (finite_content nu (prefixContent c r)).fintype

theorem fiber_bounded (c : ℕ → ℕ) (r : ℕ) (T : Fiber c r nu) : InAlphabet r T.val := by
  intro p hp
  have hm := entry_mem_support T.val hp
  rw [T.property, Finsupp.mem_support_iff] at hm
  by_contra hn
  exact hm (prefixContent_above c (by omega))

theorem content_above (T : PositiveTableau nu) (r : ℕ) (hb : InAlphabet r T)
    {k : ℕ} (hk : r < k) : content T k = 0 := by
  rw [content_apply]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp
  have := hb p hp
  omega

theorem prefix_content_apply (T : PositiveTableau nu) (r k : ℕ) :
    content (prefixTableau T r) k = if k ≤ r then content T k else 0 := by
  by_cases hk : k ≤ r
  · rw [if_pos hk, content_apply, content_apply]
    congr 1
    ext p
    simp only [Finset.mem_filter, mem_prefix]
    constructor
    · rintro ⟨⟨hp,hr⟩,he⟩
      rw [prefix_entry T r (Finset.mem_filter.mpr ⟨hp,hr⟩)] at he
      exact ⟨hp,he⟩
    · rintro ⟨hp,he⟩
      have hr : T.entry p.1 p.2 ≤ r := he ▸ hk
      exact ⟨⟨hp,hr⟩, by rw [prefix_entry T r (Finset.mem_filter.mpr ⟨hp,hr⟩), he]⟩
  · rw [if_neg hk]
    exact content_above _ r (prefix_bounded T r) (by omega)

theorem fiber_prefix_content (c : ℕ → ℕ) (r : ℕ) (T : Fiber c (r+1) nu) :
    content (prefixTableau T.val r) = prefixContent c r := by
  ext k
  rw [prefix_content_apply, T.property, prefixContent_succ, Finsupp.add_apply,
    Finsupp.single_apply]
  by_cases hk : k ≤ r
  · rw [if_pos hk, if_neg (by omega : r+1 ≠ k), Nat.add_zero]
  · rw [if_neg hk, prefixContent_above c (by omega : r < k)]

theorem fiber_prefix_degree (c : ℕ → ℕ) (r : ℕ) (T : Fiber c (r+1) nu) :
    (prefixShape T.val r).card = prefixDegree c r := by
  rw [← content_total (prefixTableau T.val r), fiber_prefix_content c r T, prefixContent_total]

attribute [local instance] degreeFintype

abbrev FiberStep (c : ℕ → ℕ) (r : ℕ) (nu : YoungDiagram) :=
  Σ mu : {mu : DegreeShape (prefixDegree c r) // Horizontal mu.val nu}, Fiber c r mu.val.val

theorem step_card (c : ℕ → ℕ) (r : ℕ)
    (u : DegreeShape (prefixDegree c r)) (v : DegreeShape (prefixDegree c (r+1)))
    (hh : Horizontal u.val v.val) : (v.val.cells \ u.val.cells).card = c (r+1) := by
  rw [Finset.card_sdiff hh.1]
  change v.val.card - u.val.card = _
  rw [u.property, v.property, prefixDegree_succ, Nat.add_sub_cancel_left]

def fiberStepMap (c : ℕ → ℕ) (r : ℕ) (v : DegreeShape (prefixDegree c (r+1)))
    (x : FiberStep c r v.val) : Fiber c (r+1) v.val :=
  ⟨extendTableau x.2.val r (fiber_bounded c r x.2) x.1.property, by
    rw [extend_content, x.2.property, step_card c r x.1.val v x.1.property,
      prefixContent_succ]⟩

theorem fiberStepMap_bijective (c : ℕ → ℕ) (r : ℕ) (v : DegreeShape (prefixDegree c (r+1))) :
    Function.Bijective (fiberStepMap c r v) := by
  constructor
  · rintro ⟨⟨⟨mu,hd⟩,hm⟩,T,hT⟩ ⟨⟨⟨mu',hd'⟩,hm'⟩,T',hT'⟩ he
    have ht := congrArg Subtype.val he
    change extendTableau T r (fiber_bounded c r ⟨T,hT⟩) hm =
      extendTableau T' r (fiber_bounded c r ⟨T',hT'⟩) hm' at ht
    have hs := congrArg (fun S => prefixShape S r) ht
    dsimp only at hs
    rw [prefix_extend_shape, prefix_extend_shape] at hs
    subst mu'
    have ht' : T = T' := by
      apply ext_cells
      intro p hp
      have hh := congrArg (fun S : PositiveTableau v.val => S.entry p.1 p.2) ht
      simpa only [extend_old _ _ _ _ hp] using hh
    subst T'
    rfl
  · intro T
    refine ⟨⟨⟨⟨prefixShape T.val r, fiber_prefix_degree c r T⟩,
      prefix_horizontal T.val r (fiber_bounded c (r+1) T)⟩,
      ⟨prefixTableau T.val r,fiber_prefix_content c r T⟩⟩, ?_⟩
    apply Subtype.ext
    exact extend_prefix T.val r (fiber_bounded c (r+1) T)

/-- The actual fixed-content recording bijection on exhaustive degree shapes. -/
def fiberStepEquiv (c : ℕ → ℕ) (r : ℕ) (v : DegreeShape (prefixDegree c (r+1))) :
    FiberStep c r v.val ≃ Fiber c (r+1) v.val :=
  Equiv.ofBijective _ (fiberStepMap_bijective c r v)

/-- NE^< as a literal count of ordered pairs of actual cells. -/
def neLess (T : PositiveTableau nu) : ℕ :=
  ∑ p ∈ nu.cells, (nu.cells.filter (fun q =>
    q.1 < p.1 ∧ p.2 < q.2 ∧ T.entry q.1 q.2 < T.entry p.1 p.2)).card

/-- An old cell strictly right of a new one is necessarily above it. -/
theorem old_right_above {p q : ℕ × ℕ}
    (hp : p ∈ nu.cells \ mu.cells) (hq : q ∈ mu.cells) (hc : p.2 < q.2) : q.1 < p.1 := by
  by_contra hn
  exact (Finset.mem_sdiff.mp hp).2 (mu.up_left_mem (by omega) hc.le hq)

/-- Exact NE^< recurrence: only old/right pairs with the newly added label appear. -/
theorem neLess_extend (T : PositiveTableau mu) (r : ℕ) (hb : InAlphabet r T)
    (hh : Horizontal mu nu) :
    neLess (extendTableau T r hb hh) = neLess T + stripCount mu nu := by
  let S := extendTableau T r hb hh
  have old (p : ℕ × ℕ) (hp : p ∈ mu.cells) :
      (nu.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2 ∧ S.entry q.1 q.2 < S.entry p.1 p.2)) =
      mu.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2 ∧ T.entry q.1 q.2 < T.entry p.1 p.2) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq,hr,hc,he⟩
      have hqm : q ∈ mu.cells := by
        by_contra hn
        have hs := extend_new T r hb hh (Finset.mem_sdiff.mpr ⟨hq,hn⟩)
        have hsp := extend_old T r hb hh hp
        have htp := hb p hp
        change S.entry q.1 q.2 = r+1 at hs
        change S.entry p.1 p.2 = T.entry p.1 p.2 at hsp
        omega
      exact ⟨hqm,hr,hc, by simpa only [S,extend_old T r hb hh hqm,extend_old T r hb hh hp] using he⟩
    · rintro ⟨hq,hr,hc,he⟩
      exact ⟨hh.1 hq,hr,hc,by simpa only [S,extend_old T r hb hh hq,extend_old T r hb hh hp] using he⟩
  have fresh (p : ℕ × ℕ) (hp : p ∈ nu.cells \ mu.cells) :
      (nu.cells.filter (fun q => q.1 < p.1 ∧ p.2 < q.2 ∧ S.entry q.1 q.2 < S.entry p.1 p.2)) =
      mu.cells.filter (fun q => p.2 < q.2) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq,_hr,hc,he⟩
      have hqm : q ∈ mu.cells := by
        by_contra hn
        have hsq := extend_new T r hb hh (Finset.mem_sdiff.mpr ⟨hq,hn⟩)
        have hsp := extend_new T r hb hh hp
        change S.entry q.1 q.2 = r+1 at hsq
        change S.entry p.1 p.2 = r+1 at hsp
        omega
      exact ⟨hqm,hc⟩
    · rintro ⟨hq,hc⟩
      refine ⟨hh.1 hq,old_right_above hp hq hc,hc,?_⟩
      dsimp only [S]
      rw [extend_old T r hb hh hq, extend_new T r hb hh hp]
      exact Nat.lt_succ_of_le (hb q hq)
  unfold neLess
  change (∑ p ∈ nu.cells, (nu.cells.filter (fun q =>
    q.1 < p.1 ∧ p.2 < q.2 ∧ S.entry q.1 q.2 < S.entry p.1 p.2)).card) = _
  rw [← Finset.sum_sdiff hh.1, add_comm]
  apply congrArg₂ (· + ·)
  · exact Finset.sum_congr rfl (fun p hp => congrArg Finset.card (old p hp))
  · exact Finset.sum_congr rfl (fun p hp => congrArg Finset.card (fresh p hp))

open OddMath.LrLegA TableauRowWord

private theorem countNorth_sum (as : Tableau) (B : TBox) :
    countNorth as B = (as.map (fun A => if A.row < B.row then 1 else 0)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih => simp [countNorth,isNorth,ih]

private theorem countNE_sum (as : Tableau) (B : TBox) :
    countNE as B = (as.map (fun A => if A.row < B.row ∧ B.col < A.col then 1 else 0)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    simp [countNE,isNorth,isEast,ih]
    split_ifs <;> simp_all

private theorem countNELt_sum (as : Tableau) (B : TBox) :
    countNELt as B = (as.map (fun A =>
      if A.row < B.row ∧ B.col < A.col ∧ A.entry < B.entry then 1 else 0)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    simp [countNELt,isNorth,isEast,isLtEntry,ih,and_assoc]
    split_ifs <;> simp_all

private theorem countNorthLt_sum (as : Tableau) (B : TBox) :
    countNorthLt as B = (as.map (fun A =>
      if A.row < B.row ∧ A.entry < B.entry then 1 else 0)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    simp [countNorthLt,isNorth,isLtEntry,ih]
    split_ifs <;> simp_all

private theorem total_sums (as bs : Tableau) :
    totalNorth as bs = (bs.map (countNorth as)).sum ∧
    totalNE as bs = (bs.map (countNE as)).sum ∧
    totalNELt as bs = (bs.map (countNELt as)).sum ∧
    totalNorthLt as bs = (bs.map (countNorthLt as)).sum := by
  induction bs with
  | nil => simp [totalNorth,totalNE,totalNELt,totalNorthLt]
  | cons B bs ih => simp only [totalNorth,totalNE,totalNELt,totalNorthLt,List.map_cons,
      List.sum_cons,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,and_self]

theorem totalNorth_shape (T : PositiveTableau nu) : totalNorth (boxes T) (boxes T) = north nu := by
  rw [(total_sums _ _).1]
  simp [boxes, countNorth_sum, List.map_map, box, Finset.sum_boole, north]

theorem totalNE_shape (T : PositiveTableau nu) : totalNE (boxes T) (boxes T) = northEast nu := by
  rw [(total_sums _ _).2.1]
  simp [boxes, countNE_sum, List.map_map, box, Finset.sum_boole, northEast]

theorem totalNELt_neLess (T : PositiveTableau nu) : totalNELt (boxes T) (boxes T) = neLess T := by
  rw [(total_sums _ _).2.2.1]
  simp [boxes, countNELt_sum, List.map_map, box, Finset.sum_boole, neLess]

/-- Exact requested source sign identity on actual recording tableaux. -/
theorem recording_sign (T : PositiveTableau nu) :
    (-1 : ℤ) ^ (northEast nu + neLess T) = (-1 : ℤ) ^ north nu * tableauSign T := by
  have h := TableauSign.global_sign T
  simpa only [signLeft,signRight,totalNE_shape,totalNELt_neLess,totalNorth_shape,
    pow_add,tableauSign,rowWord_inversions] using h

theorem canonical_sign (nu : YoungDiagram) : tableauSign (canonicalTableau nu) = (-1 : ℤ) ^ north nu := by
  unfold tableauSign
  rw [rowWord_inversions, (total_sums _ _).2.2.2]
  congr 1
  simp only [boxes, List.map_map, countNorthLt_sum, box, Function.comp_apply,
    Finset.sum_map_toList]
  unfold north
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  simp [canonical_entry hp, canonical_entry hq]

/-- The one-strip Pieri normalization; (-1)^NE times the source s^p. -/
def pieriSp (n : ℕ) (nu : YoungDiagram) : SkewPolynomial n :=
  (-1 : ℤ) ^ shapeExponent nu • tableauPolynomial n nu

/-- Recording coefficients are genuine fixed-content SSYT sums. -/
def recordCoeff (c : ℕ → ℕ) (r : ℕ) (nu : YoungDiagram) : ℤ :=
  ∑ T : Fiber c r nu, (-1 : ℤ) ^ neLess T.val

/-- Complete factors are ordered in increasing recording-label order. -/
def prefixProduct (n : ℕ) (c : ℕ → ℕ) (r : ℕ) : SkewPolynomial n :=
  ((List.range r).map (fun i => completePoly n (c (i+1)))).prod

@[simp] theorem prefixProduct_succ (n : ℕ) (c : ℕ → ℕ) (r : ℕ) :
    prefixProduct n c (r+1) = prefixProduct n c r * completePoly n (c (r+1)) := by
  simp [prefixProduct,List.range_succ,List.map_append,List.prod_append,_root_.mul_one]

theorem recordCoeff_succ (c : ℕ → ℕ) (r : ℕ) (v : DegreeShape (prefixDegree c (r+1))) :
    recordCoeff c (r+1) v.val = ∑ u : DegreeShape (prefixDegree c r),
      if Horizontal u.val v.val then recordCoeff c r u.val * (-1 : ℤ) ^ stripCount u.val v.val else 0 := by
  unfold recordCoeff
  rw [← (fiberStepEquiv c r v).sum_comp (fun T => (-1 : ℤ) ^ neLess T.val)]
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ u : {u : DegreeShape (prefixDegree c r) // Horizontal u.val v.val},
        (∑ T : Fiber c r u.val.val, (-1 : ℤ) ^ neLess T.val) * (-1 : ℤ) ^ stripCount u.val.val v.val := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T _
      change (-1 : ℤ) ^ neLess (extendTableau T.val r (fiber_bounded c r T) u.property) = _
      rw [neLess_extend, pow_add]
    _ = ∑ u ∈ Finset.univ.filter (fun u : DegreeShape (prefixDegree c r) => Horizontal u.val v.val),
        (∑ T : Fiber c r u.val, (-1 : ℤ) ^ neLess T.val) * (-1 : ℤ) ^ stripCount u.val v.val :=
      (Finset.sum_subtype (p := fun u : DegreeShape (prefixDegree c r) => Horizontal u.val v.val)
        (Finset.univ.filter (fun u => Horizontal u.val v.val)) (by simp)
        (fun u => (∑ T : Fiber c r u.val, (-1 : ℤ) ^ neLess T.val) *
          (-1 : ℤ) ^ stripCount u.val v.val)).symm
    _ = _ := by rw [Finset.sum_filter]

theorem pieriSp_mul (n d k : ℕ) (u : DegreeShape d) :
    pieriSp n u.val * completePoly n k = ∑ v : DegreeShape (d+k),
      if Horizontal u.val v.val then (-1 : ℤ) ^ stripCount u.val v.val • pieriSp n v.val else 0 := by
  have h := horizontal_pieri n u.val k
  rw [u.property] at h
  rw [pieriSp, smul_mul_assoc, h]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · rw [pieriSp, ← mul_smul, ← pow_add, Nat.add_comm]
  · rfl

def degreeZero : DegreeShape 0 := ⟨⊥,rfl⟩

theorem degree_zero_unique (u : DegreeShape 0) : u = degreeZero := by
  apply Subtype.ext
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp u.property

theorem recordCoeff_empty (c : ℕ → ℕ) : recordCoeff c 0 ⊥ = 1 := by
  letI : Unique (Fiber c 0 ⊥) :=
    { default := ⟨emptyTableau, by simp [content,prefixContent]⟩
      uniq := by intro T; apply Subtype.ext; apply ext_cells; simp }
  rw [recordCoeff, Fintype.sum_unique]
  simp [neLess]

/-- Empty start, including the empty alphabet. -/
theorem prefix_expansion_zero (n : ℕ) (c : ℕ → ℕ) :
    prefixProduct n c 0 = ∑ u : DegreeShape (prefixDegree c 0), recordCoeff c 0 u.val • pieriSp n u.val := by
  change 1 = ∑ u : DegreeShape 0, recordCoeff c 0 u.val • pieriSp n u.val
  letI : Unique (DegreeShape 0) := { default := degreeZero, uniq := degree_zero_unique }
  rw [Fintype.sum_unique]
  change 1 = recordCoeff c 0 ⊥ • pieriSp n ⊥
  simp [recordCoeff_empty,pieriSp,shapeExponent,directNorth,north,northEast]

/-- Full ordered complete-product expansion, before converting its signs to K. -/
theorem prefix_expansion (n : ℕ) (c : ℕ → ℕ) (r : ℕ) :
    prefixProduct n c r = ∑ u : DegreeShape (prefixDegree c r), recordCoeff c r u.val • pieriSp n u.val := by
  induction r with
  | zero => exact prefix_expansion_zero n c
  | succ r ih =>
    rw [prefixProduct_succ, ih, Finset.sum_mul]
    simp_rw [smul_mul_assoc, pieriSp_mul]
    rw [prefixDegree_succ]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    have hc := recordCoeff_succ c r (show DegreeShape (prefixDegree c (r+1)) from
      ⟨v.val, v.property.trans (prefixDegree_succ c r).symm⟩)
    rw [hc, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp only [smul_smul, smul_zero, zero_smul]

@[simp] theorem prefixContent_zero_apply (c : ℕ → ℕ) (r : ℕ) : prefixContent c r 0 = 0 := by
  simp [prefixContent,Finsupp.finset_sum_apply,Finsupp.single_apply]

theorem prefixContent_apply_succ (c : ℕ → ℕ) (r k : ℕ) :
    prefixContent c r (k+1) = if k < r then c (k+1) else 0 := by
  simp [prefixContent,Finsupp.finset_sum_apply,Finsupp.single_apply]

theorem prefixContent_eq (c : ℕ →₀ ℕ) (r : ℕ) (h0 : c 0 = 0)
    (hb : ∀ k ∈ c.support, k ≤ r) : prefixContent c r = c := by
  ext k
  cases k with
  | zero => rw [prefixContent_zero_apply,h0]
  | succ k =>
    rw [prefixContent_apply_succ]
    split_ifs with hk
    · rfl
    · symm
      apply Finsupp.not_mem_support_iff.mp
      intro hm
      have := hb (k+1) hm
      omega

theorem shape_row_bound (mu : YoungDiagram) (p : ℕ × ℕ) (hp : p ∈ mu.cells) : p.1 < mu.colLen 0 := by
  apply YoungDiagram.mem_iff_lt_colLen.mp
  exact mu.up_left_mem le_rfl (Nat.zero_le _) hp

theorem prefixContent_shape (mu : YoungDiagram) :
    prefixContent (shapeContent mu) (mu.colLen 0) = shapeContent mu := by
  apply prefixContent_eq
  · rw [← content_canonical]; exact content_zero _
  · exact shapeContent_bounded _ mu (shape_row_bound mu)

theorem prefixDegree_shape (mu : YoungDiagram) : prefixDegree (shapeContent mu) (mu.colLen 0) = mu.card := by
  rw [← prefixContent_total, prefixContent_shape, ← content_canonical, content_total]

/-- The order is literally the source row-length list, not a commuted product. -/
theorem prefixProduct_shape (n : ℕ) (mu : YoungDiagram) :
    prefixProduct n (shapeContent mu) (mu.colLen 0) = H n mu := by
  simp only [prefixProduct,H,YoungDiagram.rowLens,List.map_map,Function.comp_def,
    SignedKostkaInvertibility.shapeContent_row]

theorem recordCoeff_kostka (c : ℕ → ℕ) (r : ℕ) (mu lam : YoungDiagram)
    (hc : prefixContent c r = shapeContent mu) :
    recordCoeff c r lam * (-1 : ℤ) ^ northEast lam = signedKostka lam mu := by
  unfold recordCoeff signedKostka
  rw [canonical_sign, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ T : Fiber c r lam, (-1 : ℤ) ^ north lam * tableauSign T.val := by
      apply Finset.sum_congr rfl
      intro T _
      rw [mul_comm, ← pow_add, recording_sign]
    _ = _ := (Finset.sum_subtype (p := fun T : PositiveTableau lam => content T = prefixContent c r)
      (tableauxOfContent lam (shapeContent mu))
      (fun T => by rw [mem_tableauxOfContent, hc])
      (fun T => (-1 : ℤ) ^ north lam * tableauSign T)).symm

theorem pieriSp_eq (n : ℕ) (lam : YoungDiagram) :
    pieriSp n lam = (-1 : ℤ) ^ northEast lam • sp n lam := by
  unfold pieriSp sp shapeExponent
  rw [← mul_smul, ← pow_add, Nat.add_comm]

theorem recordCoeff_smul (n : ℕ) (c : ℕ → ℕ) (r : ℕ) (mu lam : YoungDiagram)
    (hc : prefixContent c r = shapeContent mu) :
    recordCoeff c r lam • pieriSp n lam = signedKostka lam mu • sp n lam := by
  rw [pieriSp_eq, ← mul_smul, recordCoeff_kostka c r mu lam hc]

/-- Ellis Theorem 3.8, the actual complete-product premise (M5).
All shapes of the degree are included; no recording/sign/expansion premise remains. -/
theorem complete_tableau_expansion_shape (n : ℕ) (mu : YoungDiagram) :
    H n mu = ∑ lam : DegreeShape mu.card, signedKostka lam.val mu • sp n lam.val := by
  have h := prefix_expansion n (shapeContent mu) (mu.colLen 0)
  rw [prefixProduct_shape, prefixDegree_shape] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro lam _
  exact recordCoeff_smul n (shapeContent mu) (mu.colLen 0) mu lam.val (prefixContent_shape mu)

/-- Exhaustive-degree form for the inherited module-valued Kostka inverse. -/
theorem complete_tableau_expansion (n d : ℕ) (mu : DegreeShape d) :
    H n mu.val = ∑ lam : DegreeShape d, signedKostka lam.val mu.val • sp n lam.val := by
  rcases mu with ⟨mu, rfl⟩
  exact complete_tableau_expansion_shape n mu

/-- Every actual ordered complete product is already in the joint kernel. -/
theorem H_mem (n : ℕ) (mu : YoungDiagram) : H (n+2) mu ∈ OddSymmetricKernel.kernelSubring n := by
  unfold H
  apply (OddSymmetricKernel.kernelSubring n).list_prod_mem
  intro f hf
  obtain ⟨k,_hk,rfl⟩ := List.mem_map.mp hf
  exact OddSymmetricKernel.complete_mem n k

/-- Now the inverse is a consequence of the literal expansion, not a definition. -/
theorem sp_recovered (n d : ℕ) :
    KostkaModuleInversion.recover d (fun mu : DegreeShape d => H n mu.val) =
      (fun lam : DegreeShape d => sp n lam.val) := by
  have he : (fun mu : DegreeShape d => H n mu.val) =
      KostkaModuleInversion.transform d (fun lam : DegreeShape d => sp n lam.val) := by
    funext mu
    exact complete_tableau_expansion n d mu
  rw [he, KostkaModuleInversion.leftInverse]

/-- No complete-expansion premise remains in the kernel consequence. -/
theorem sp_mem (n : ℕ) (mu : YoungDiagram) : sp (n+2) mu ∈ OddSymmetricKernel.kernelSubring n := by
  let A := (OddSymmetricKernel.kernelSubring n).toAddSubgroup.toIntSubmodule
  have h := (KostkaModuleInversion.submoduleTarget mu.card A
    (fun lam : DegreeShape mu.card => sp (n+2) lam.val)).mp
  apply h _ ⟨mu,rfl⟩
  intro j
  change (∑ lam : DegreeShape mu.card, signedKostka lam.val j.val • sp (n+2) lam.val) ∈
    OddSymmetricKernel.kernelSubring n
  rw [← complete_tableau_expansion]
  exact H_mem n j.val

/-- Unconditional membership for the inherited RAW tableau polynomial. -/
theorem tableauPolynomial_mem (n : ℕ) (mu : YoungDiagram) :
    tableauPolynomial (n+2) mu ∈ OddSymmetricKernel.kernelSubring n := by
  have h := (OddSymmetricKernel.kernelSubring n).zsmul_mem (sp_mem n mu)
    ((-1 : ℤ) ^ (directNorth mu + north mu))
  simpa only [sp,smul_smul,← mul_pow,neg_mul_neg,_root_.one_mul,one_pow,one_smul] using h

/-- Every actual adjacent odd divided difference annihilates every tableau sum. -/
theorem divided_tableauPolynomial (n : ℕ) (mu : YoungDiagram) (i : Fin (n+1)) :
    AllRankDivided.divided i (tableauPolynomial (n+2) mu) = 0 := tableauPolynomial_mem n mu i

end
end OddMath.Frontier.CompleteTableauExpansion
