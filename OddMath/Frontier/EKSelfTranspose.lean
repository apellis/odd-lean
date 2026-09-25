import OddMath.Frontier.EKSemiorthogonality

/-! EK 1107.5610v2 pp.23–24: diagonal hooks, independently of (3.4).
A frame stores the endpoints of the diagonal rows, not a surrogate diagram. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace OddMath.Frontier.EKSelfTranspose

def SelfTranspose (n : ℕ) :=
  {μ : DegreeShapes.DegreeShape n // μ.val.transpose = μ.val}
def DistinctOddParts (n : ℕ) :=
  {parts : List ℕ // parts.Pairwise (· > ·) ∧
    (∀ a ∈ parts, 0 < a ∧ Odd a) ∧ parts.sum = n}

structure Frame where
  d : ℕ
  ends : Fin d → ℕ
  anti : Antitone ends
  diag : ∀ i, i.val < ends i

/-- Membership described by the unique diagonal hook containing a cell. -/
def Frame.Contains (f : Frame) (p : ℕ × ℕ) : Prop :=
  ∃ h : min p.1 p.2 < f.d, max p.1 p.2 < f.ends ⟨min p.1 p.2, h⟩

instance (f : Frame) (p : ℕ × ℕ) : Decidable (f.Contains p) := Classical.propDecidable _

theorem Frame.lower (f : Frame) {p q : ℕ × ℕ} (hpq : p ≤ q)
    (hq : f.Contains q) : f.Contains p := by
  obtain ⟨hq, he⟩ := hq
  have hm : min p.1 p.2 ≤ min q.1 q.2 := min_le_min hpq.1 hpq.2
  refine ⟨lt_of_le_of_lt hm hq, ?_⟩
  exact lt_of_le_of_lt (max_le_max hpq.1 hpq.2)
    (lt_of_lt_of_le he (f.anti (show (⟨min p.1 p.2, _⟩ : Fin f.d) ≤ ⟨min q.1 q.2,hq⟩ from hm)))

def Frame.bound (f : Frame) : ℕ := ∑ i, f.ends i

def Frame.diagram (f : Frame) : YoungDiagram where
  cells := (Finset.range f.bound ×ˢ Finset.range f.bound).filter f.Contains
  isLowerSet := by
    intro p q hpq hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
    exact ⟨⟨lt_of_le_of_lt hpq.1 hq.1.1, lt_of_le_of_lt hpq.2 hq.1.2⟩, f.lower hpq hq.2⟩

@[simp] theorem Frame.mem_diagram (f : Frame) (p : ℕ × ℕ) : p ∈ f.diagram ↔ f.Contains p := by
  change p ∈ (Finset.range f.bound ×ˢ Finset.range f.bound).filter f.Contains ↔ _
  rw [Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨hi, he⟩ := h
  have hb : f.ends ⟨min p.1 p.2,hi⟩ ≤ f.bound :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le he hb),
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le he hb)⟩

@[simp] theorem Frame.diagonal (f : Frame) (i : ℕ) : (i,i) ∈ f.diagram ↔ i < f.d := by
  simp only [f.mem_diagram, Contains, min_self, max_self]
  exact ⟨fun ⟨h,_⟩ => h, fun h => ⟨h, f.diag ⟨i,h⟩⟩⟩

theorem Frame.transpose (f : Frame) : f.diagram.transpose = f.diagram := by
  apply SetLike.coe_injective
  ext p
  simp only [SetLike.mem_coe, YoungDiagram.mem_transpose, mem_diagram, Contains,
    Prod.fst_swap, Prod.snd_swap, min_comm p.2 p.1, max_comm p.2 p.1]

theorem Frame.rowLen (f : Frame) (i : Fin f.d) : f.diagram.rowLen i = f.ends i := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · intro hj
    by_cases hji : j < i
    · exact lt_trans hji (f.diag i)
    · have h := (f.mem_diagram _).mp hj
      simp only [Contains, min_eq_left (show i.val ≤ j by omega),
        max_eq_right (show i.val ≤ j by omega)] at h
      exact h.choose_spec
  · intro hj
    by_cases hji : j < i
    · exact f.diagram.up_left_mem (le_refl _) (Nat.le_of_lt hji) ((f.diagonal i).mpr i.isLt)
    · apply (f.mem_diagram _).mpr
      simpa only [Contains, min_eq_left (show i.val ≤ j by omega),
        max_eq_right (show i.val ≤ j by omega)] using (⟨i.isLt, hj⟩ : ∃ h : i.val < f.d, j < f.ends ⟨i.val,h⟩)

def rank (μ : YoungDiagram) : ℕ :=
  Nat.find (show ∃ i, (i,i) ∉ μ from ⟨μ.card, fun h =>
    (Nat.lt_irrefl μ.card) (DegreeShapes.cell_lt_card μ (μ.card,μ.card) h).1⟩)

theorem diagonal_iff (μ : YoungDiagram) (i : ℕ) : (i,i) ∈ μ ↔ i < rank μ := by
  unfold rank
  rw [Nat.lt_find_iff]
  push_neg
  exact ⟨fun h j hj => μ.up_left_mem hj hj h, fun h => h i le_rfl⟩

def frameOf (μ : YoungDiagram) : Frame where
  d := rank μ
  ends i := μ.rowLen i
  anti := fun i j h => μ.rowLen_anti i j h
  diag i := YoungDiagram.mem_iff_lt_rowLen.mp ((diagonal_iff μ i).mpr i.isLt)

theorem swap_mem {μ : YoungDiagram} (hμ : μ.transpose = μ) (p : ℕ × ℕ) :
    p.swap ∈ μ ↔ p ∈ μ := by rw [← YoungDiagram.mem_transpose, hμ]

theorem frameOf_diagram (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    (frameOf μ).diagram = μ := by
  apply SetLike.coe_injective
  ext ⟨i,j⟩
  simp only [SetLike.mem_coe, Frame.mem_diagram, Frame.Contains, frameOf]
  by_cases hij : i ≤ j
  · simp only [min_eq_left hij, max_eq_right hij]
    constructor
    · rintro ⟨_,h⟩; exact YoungDiagram.mem_iff_lt_rowLen.mpr h
    · intro h
      exact ⟨(diagonal_iff μ i).mp (μ.up_left_mem le_rfl hij h),
        YoungDiagram.mem_iff_lt_rowLen.mp h⟩
  · have hji : j ≤ i := by omega
    simp only [min_eq_right hji, max_eq_left hji]
    rw [← swap_mem hμ (i,j)]
    constructor
    · rintro ⟨_,h⟩; exact YoungDiagram.mem_iff_lt_rowLen.mpr h
    · intro h
      exact ⟨(diagonal_iff μ j).mp (μ.up_left_mem le_rfl hji h),
        YoungDiagram.mem_iff_lt_rowLen.mp h⟩

/-- Actual descending diagonal hook lengths. -/
def hooks (μ : YoungDiagram) : List ℕ :=
  List.ofFn (fun i : Fin (rank μ) => 2 * (μ.rowLen i - i.val) - 1)

theorem hooks_get (μ : YoungDiagram) (i : Fin (rank μ)) :
    (hooks μ)[i.val]'(by simp [hooks]) = 2 * (μ.rowLen i - i.val) - 1 := by simp [hooks]

theorem hooks_positive_odd (μ : YoungDiagram) : ∀ a ∈ hooks μ, 0 < a ∧ Odd a := by
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  have hi := (frameOf μ).diag i
  change i.val < μ.rowLen i at hi
  constructor
  · omega
  · exact ⟨μ.rowLen i - i.val - 1, by omega⟩

theorem hooks_descending (μ : YoungDiagram) : (hooks μ).Pairwise (· > ·) := by
  rw [hooks, List.pairwise_ofFn]
  intro i j hij
  have hi := (frameOf μ).diag i
  have hj := (frameOf μ).diag j
  have hm := μ.rowLen_anti i j (Nat.le_of_lt hij)
  change i.val < μ.rowLen i at hi
  change j.val < μ.rowLen j at hj
  change i.val < j.val at hij
  omega

/-- The hook based at (i,i), with its corner counted just once. -/
def hookCells (μ : YoungDiagram) (i : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter (fun p => min p.1 p.2 = i)

theorem hookCells_eq (μ : YoungDiagram) (i : ℕ) :
    hookCells μ i = ({i} ×ˢ Finset.Ico i (μ.rowLen i)) ∪
      (Finset.Ico (i+1) (μ.colLen i) ×ˢ {i}) := by
  ext ⟨a,b⟩
  simp only [hookCells, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_union,
    Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
  constructor
  · rintro ⟨hp,hm⟩
    by_cases ha : a = i
    · subst a
      exact Or.inl ⟨rfl, by omega, YoungDiagram.mem_iff_lt_rowLen.mp hp⟩
    · have hb : b = i := by omega
      subst b
      exact Or.inr ⟨⟨by omega, YoungDiagram.mem_iff_lt_colLen.mp hp⟩,rfl⟩
  · rintro (⟨rfl,hi,hb⟩ | ⟨⟨hi,ha⟩,rfl⟩)
    · exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hb, by omega⟩
    · exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr ha, by omega⟩

theorem hookCells_card (μ : YoungDiagram) (i : ℕ) :
    (hookCells μ i).card = (μ.rowLen i - i) + (μ.colLen i - (i+1)) := by
  rw [hookCells_eq, Finset.card_union_of_disjoint]
  · simp
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at hp hq
    omega

theorem hookCells_card_self (μ : YoungDiagram) (hμ : μ.transpose = μ)
    (i : ℕ) (hi : (i,i) ∈ μ) :
    (hookCells μ i).card = 2 * (μ.rowLen i - i) - 1 := by
  rw [hookCells_card, ← YoungDiagram.rowLen_transpose, hμ]
  have := YoungDiagram.mem_iff_lt_rowLen.mp hi
  omega

theorem hooks_sum (μ : YoungDiagram) (hμ : μ.transpose = μ) : (hooks μ).sum = μ.card := by
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := μ.cells) (t := Finset.range (rank μ)) (f := fun p : ℕ × ℕ => min p.1 p.2)
    (fun p hp => Finset.mem_range.mpr ((diagonal_iff μ _).mp
      (μ.up_left_mem (min_le_left _ _) (min_le_right _ _) hp)))
  rw [Finset.sum_range] at hc
  rw [hooks, List.sum_ofFn]
  change (∑ i : Fin (rank μ), (2 * (μ.rowLen i - i.val) - 1)) = μ.cells.card
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  exact (hookCells_card_self μ hμ i ((diagonal_iff μ i).mpr i.isLt)).symm

@[simp] theorem Frame.rank (f : Frame) : rank f.diagram = f.d := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← diagonal_iff, f.diagonal]

/-- The list-side data before restriction to a fixed weight. -/
def OddParts := {parts : List ℕ // parts.Pairwise (· > ·) ∧
  ∀ a ∈ parts, 0 < a ∧ Odd a}

def partEnd (p : OddParts) (i : Fin p.val.length) : ℕ := i.val + 1 + (p.val[i.val] - 1)/2

private theorem fin_antitone_of_next {n : ℕ} (f : Fin n → ℕ)
    (h : ∀ i j, j.val = i.val + 1 → f j ≤ f i) : Antitone f := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n => exact Fin.antitone_iff_succ_le.mpr (fun i => h i.castSucc i.succ rfl)

theorem partEnd_anti (p : OddParts) : Antitone (partEnd p) := by
  apply fin_antitone_of_next
  intro i j hij
  have h := (List.pairwise_iff_getElem.mp p.property.1) i.val j.val
    i.isLt j.isLt (by omega)
  have hi := p.property.2 p.val[i.val] (List.getElem_mem i.isLt)
  have hj := p.property.2 p.val[j.val] (List.getElem_mem j.isLt)
  obtain ⟨a,ha⟩ := hi.2
  obtain ⟨b,hb⟩ := hj.2
  simp only [partEnd]
  omega

def ofPartsFrame (p : OddParts) : Frame where
  d := p.val.length
  ends := partEnd p
  anti := partEnd_anti p
  diag i := by dsimp [partEnd]; omega

def ofParts (p : OddParts) : YoungDiagram := (ofPartsFrame p).diagram

@[simp] theorem ofParts_self (p : OddParts) : (ofParts p).transpose = ofParts p :=
  (ofPartsFrame p).transpose

theorem hooks_ofParts (p : OddParts) : hooks (ofParts p) = p.val := by
  apply List.ext_getElem
  · simp [hooks, ofParts, ofPartsFrame]
  · intro i hi hj
    have hr : rank (ofParts p) = p.val.length := (ofPartsFrame p).rank
    have hrow := (ofPartsFrame p).rowLen ⟨i,hj⟩
    change (ofParts p).rowLen i = partEnd p ⟨i,hj⟩ at hrow
    simp only [hooks, List.getElem_ofFn, hrow, partEnd]
    have ha := p.property.2 p.val[i] (List.getElem_mem hj)
    obtain ⟨a,ha'⟩ := ha.2
    omega

theorem hooks_injective : Function.Injective
    (fun μ : {μ : YoungDiagram // μ.transpose = μ} => hooks μ.val) := by
  intro μ ν hh
  have hr : rank μ.val = rank ν.val := by
    have := congrArg List.length hh
    simpa [hooks] using this
  have he (i : ℕ) (hi : i < rank μ.val) : μ.val.rowLen i = ν.val.rowLen i := by
    have hj : i < rank ν.val := hr ▸ hi
    have h := List.getElem_of_eq hh (by simpa [hooks] using hi)
    simp only [hooks, List.getElem_ofFn] at h
    have hμ := YoungDiagram.mem_iff_lt_rowLen.mp ((diagonal_iff μ.val i).mpr hi)
    have hν := YoungDiagram.mem_iff_lt_rowLen.mp ((diagonal_iff ν.val i).mpr hj)
    omega
  apply Subtype.ext
  rw [← frameOf_diagram μ.val μ.property, ← frameOf_diagram ν.val ν.property]
  apply SetLike.coe_injective
  ext p
  simp only [SetLike.mem_coe, Frame.mem_diagram, Frame.Contains, frameOf]
  constructor
  · rintro ⟨h,hp⟩
    exact ⟨hr ▸ h, by rwa [← he _ h]⟩
  · rintro ⟨h,hp⟩
    have h' : min p.1 p.2 < rank μ.val := hr ▸ h
    exact ⟨h', by rwa [he _ h']⟩

theorem ofParts_hooks (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    ofParts ⟨hooks μ, hooks_descending μ, hooks_positive_odd μ⟩ = μ := by
  let p : OddParts := ⟨hooks μ, hooks_descending μ, hooks_positive_odd μ⟩
  have h : (⟨ofParts p, ofParts_self p⟩ : {ν : YoungDiagram // ν.transpose = ν}) =
      ⟨μ,hμ⟩ := hooks_injective (hooks_ofParts p)
  exact congrArg Subtype.val h

/-- The genuine diagonal-hook equivalence at every weight, including zero. -/
def diagonalHookEquiv (n : ℕ) : SelfTranspose n ≃ DistinctOddParts n where
  toFun μ := ⟨hooks μ.val.val, hooks_descending _, hooks_positive_odd _,
    (hooks_sum _ μ.property).trans μ.val.property⟩
  invFun p := ⟨⟨ofParts ⟨p.val,p.property.1,p.property.2.1⟩, by
    rw [← hooks_sum _ (ofParts_self _), hooks_ofParts]
    exact p.property.2.2⟩, ofParts_self _⟩
  left_inv μ := by
    apply Subtype.ext
    apply Subtype.ext
    exact ofParts_hooks _ μ.property
  right_inv p := by
    apply Subtype.ext
    exact hooks_ofParts _

/-- Strict northeast/southwest ordered cell pairs: the literal ell statistic. -/
def crossings (μ : YoungDiagram) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (μ.cells ×ˢ μ.cells).filter (fun x => x.1.1 < x.2.1 ∧ x.2.2 < x.1.2)

def crossFlip (x : (ℕ × ℕ) × (ℕ × ℕ)) := (x.2.swap, x.1.swap)

@[simp] theorem crossFlip_twice (x : (ℕ × ℕ) × (ℕ × ℕ)) : crossFlip (crossFlip x) = x := by
  cases x; rfl

theorem ell_card (μ : YoungDiagram) : EKSemiorthogonality.ell μ = (crossings μ).card := by
  simp only [EKSemiorthogonality.ell, crossings, Finset.card_filter, Finset.sum_product]

theorem crossFlip_mem (μ : YoungDiagram) (hμ : μ.transpose = μ)
    {x : (ℕ × ℕ) × (ℕ × ℕ)} (hx : x ∈ crossings μ) : crossFlip x ∈ crossings μ := by
  simp only [crossings, Finset.mem_filter, Finset.mem_product, YoungDiagram.mem_cells,
    crossFlip, Prod.fst_swap, Prod.snd_swap] at hx ⊢
  exact ⟨⟨(swap_mem hμ x.2).mpr hx.1.2, (swap_mem hμ x.1).mpr hx.1.1⟩, hx.2.2, hx.2.1⟩

def upperCells (μ : YoungDiagram) : Finset (ℕ × ℕ) := μ.cells.filter (fun p => p.1 < p.2)

theorem fixed_crossings (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    (crossings μ).filter (fun x => crossFlip x = x) =
      (upperCells μ).image (fun p => (p,p.swap)) := by
  ext ⟨p,q⟩
  simp only [Finset.mem_filter, Finset.mem_image, crossings, Finset.mem_product,
    YoungDiagram.mem_cells, upperCells]
  constructor
  · rintro ⟨⟨⟨hp,_⟩,hx⟩,he⟩
    have hq : p.swap = q := congrArg Prod.snd he
    exact ⟨p,⟨hp,by simpa [← hq] using hx.1⟩,by simp [hq]⟩
  · rintro ⟨a,⟨ha,hab⟩,he⟩
    cases he
    exact ⟨⟨⟨ha,(swap_mem hμ p).mpr ha⟩,hab,hab⟩,by simp [crossFlip]⟩

theorem ell_sign_upper (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    (-1 : ℤ)^EKSemiorthogonality.ell μ = (-1 : ℤ)^(upperCells μ).card := by
  classical
  have hn : (∏ x ∈ (crossings μ).filter (fun x => ¬ crossFlip x = x), (-1 : ℤ)) = 1 := by
    apply Finset.prod_involution (fun x _ => crossFlip x)
    · intro x hx; norm_num
    · intro x hx _; exact (Finset.mem_filter.mp hx).2
    · intro x hx
      obtain ⟨hx,hne⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨crossFlip_mem μ hμ hx, ?_⟩
      simpa only [crossFlip_twice, ne_eq, eq_comm] using hne
    · intro x hx; exact crossFlip_twice x
  rw [ell_card, ← Finset.prod_const]
  rw [← Finset.prod_filter_mul_prod_filter_not (crossings μ) (fun x => crossFlip x = x), hn,
    mul_one, Finset.prod_const, fixed_crossings μ hμ]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

theorem upper_fiber (μ : YoungDiagram) (i : ℕ) :
    (upperCells μ).filter (fun p => p.1 = i) = {i} ×ˢ Finset.Ico (i+1) (μ.rowLen i) := by
  ext ⟨a,b⟩
  simp only [upperCells, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hp,hab⟩,rfl⟩
    exact ⟨rfl,by omega,YoungDiagram.mem_iff_lt_rowLen.mp hp⟩
  · rintro ⟨rfl,hi,hb⟩
    exact ⟨⟨YoungDiagram.mem_iff_lt_rowLen.mpr hb,by omega⟩,rfl⟩

theorem upper_card (μ : YoungDiagram) :
    (upperCells μ).card = ∑ i : Fin (rank μ), (μ.rowLen i - (i.val+1)) := by
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := upperCells μ) (t := Finset.range (rank μ)) (f := Prod.fst)
    (fun p hp => Finset.mem_range.mpr ((diagonal_iff μ _).mp
      (μ.up_left_mem le_rfl (Nat.le_of_lt (Finset.mem_filter.mp hp).2) (Finset.mem_filter.mp hp).1)))
  rw [Finset.sum_range] at hc
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [upper_fiber]
  simp

theorem hooks_half_sum (μ : YoungDiagram) :
    ((hooks μ).map (fun a => (a-1)/2)).sum = (upperCells μ).card := by
  rw [hooks, List.map_ofFn, List.sum_ofFn, upper_card]
  apply Finset.sum_congr rfl
  intro i _
  have hi := (frameOf μ).diag i
  change i.val < μ.rowLen i at hi
  dsimp [Function.comp_def]
  omega

theorem odd_half_sign (a : ℕ) (ha : Odd a) :
    (-1 : ℤ)^((a-1)/2) = if a % 4 = 3 then -1 else 1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  obtain ⟨k,hk⟩ := ha
  split_ifs with h
  · have hm : ((a-1)/2) % 2 = 1 := by omega
    simp [hm]
  · have hm : ((a-1)/2) % 2 = 0 := by omega
    simp [hm]

theorem list_half_sign (parts : List ℕ) (hp : ∀ a ∈ parts, Odd a) :
    (-1 : ℤ)^(parts.map (fun a => (a-1)/2)).sum =
      (-1 : ℤ)^(parts.countP (fun a => a % 4 = 3)) := by
  induction parts with
  | nil => simp
  | cons a parts ih =>
    have ha := hp a (by simp)
    have ht : ∀ b ∈ parts, Odd b := fun b hb => hp b (by simp [hb])
    simp only [List.map_cons, List.sum_cons, pow_add, List.countP_cons]
    rw [odd_half_sign a ha, ih ht]
    by_cases h : a % 4 = 3 <;> simp [h, pow_succ, mul_comm]

/-- EK p.24: the inherited, literal Ferrers crossing sign, not a newly defined sign. -/
theorem sign_identity (μ : YoungDiagram) (hμ : μ.transpose = μ) :
    (-1 : ℤ)^EKSemiorthogonality.ell μ =
      (-1 : ℤ)^((hooks μ).countP (fun a => a % 4 = 3)) := by
  rw [ell_sign_upper μ hμ, ← hooks_half_sum]
  exact list_half_sign _ (fun a ha => (hooks_positive_odd μ a ha).2)

/-- Existing finite enumeration of every degree-n shape, restricted to self-transposes. -/
def selfTransposeFintype (n : ℕ) : Fintype (SelfTranspose n) := by
  classical
  letI := DegreeShapes.degreeFintype n
  exact Subtype.fintype _

/-- No separate enumeration assumption: transport the genuine diagram enumeration. -/
def distinctOddPartsFintype (n : ℕ) : Fintype (DistinctOddParts n) := by
  letI := selfTransposeFintype n
  exact Fintype.ofEquiv (SelfTranspose n) (diagonalHookEquiv n)

/-- Genuine arbitrary-degree consumer. No identification with any determinant is asserted. -/
theorem sign_product_transport (n : ℕ) :
    letI := selfTransposeFintype n
    letI := distinctOddPartsFintype n
    (∏ μ : SelfTranspose n, (-1 : ℤ)^EKSemiorthogonality.ell μ.val.val) =
      ∏ p : DistinctOddParts n, (-1 : ℤ)^(p.val.countP (fun a => a % 4 = 3)) := by
  classical
  letI := selfTransposeFintype n
  letI := distinctOddPartsFintype n
  calc
    _ = ∏ μ : SelfTranspose n,
        (-1 : ℤ)^((hooks μ.val.val).countP (fun a => a % 4 = 3)) := by
      apply Finset.prod_congr rfl
      intro μ _
      exact sign_identity _ μ.property
    _ = _ := (diagonalHookEquiv n).prod_comp
      (fun p : DistinctOddParts n => (-1 : ℤ)^(p.val.countP (fun a => a % 4 = 3)))

/-- The equivalence's output is the cardinality of each actual diagonal hook. -/
theorem diagonalHookEquiv_get (n : ℕ) (μ : SelfTranspose n)
    (i : Fin (rank μ.val.val)) :
    ((diagonalHookEquiv n μ).val)[i.val]'(by simp [diagonalHookEquiv, hooks]) =
      (hookCells μ.val.val i).card := by
  change (hooks μ.val.val)[i.val]'_ = _
  rw [hooks_get, hookCells_card_self _ μ.property _ ((diagonal_iff _ _).mpr i.isLt)]

end OddMath.Frontier.EKSelfTranspose

-- All three universal obligations compiled at 20260923T201627024212Z:
-- bijection, inherited crossing sign, and finite-product transport.
