import OddMath.Frontier.OddLRVerticalPieri
import OddMath.Frontier.OddLRElimination
import OddMath.Frontier.OddLREKIdentification

/-!
# Ellis 1111.3932v1, Theorem 3.8 (3.9): s^K = s^p = s^s, assembled unconditionally

Source (frozen excerpt source excerpt, Ellis, *The odd Littlewood–Richardson
rule*, arXiv:1111.3932v1, §3.2):

  "Theorem 3.8. The three notions of odd Schur function all coincide: for any partition λ,
   (3.9)  s^K_λ = s^p_λ = s^s_λ."

  (3.4)  s^p_λ = (-1)^{dN(λ)+N(λ)} Σ_{T ∈ SSYT(λ)} x̃^{w_r(T)}      (plactic odd Schur function)
  (3.10) s^p_λ s^p_{(1^k)} = Σ_μ (-1)^{|i_1/λ| + … + |i_k/λ|} s^p_μ  (e-right Pieri rule),
         μ obtained from λ by adding a vertical strip of size k, i_1,…,i_k the rows receiving a
         box, i/λ the diagram obtained by removing rows 1 through i from λ.

Carriers (the existing ones; no new definitions of Schur functions are made here):
* s^K_λ = `OddLREKIdentification.sK λ` ∈ `EKRadicalQuotient.Q` (EK (3.6) signed-Kostka inverse of
  the complete basis), projected to N variables by `OddLREKIdentification.piN N`;
* s^p_λ = `CompleteTableauExpansion.sp N λ` ∈ `SkewPolynomial N` (sign (-1)^{dN+N} of (3.4));
* s^s_λ = `OddSymmetrizer.schur n α` ∈ `SkewPolynomial (n+2)`, α the padded row-length vector
  `OddLREKIdentification.toExponent n λ` (= `OddLRElimination.ofYoung λ`), N = n+2.

Assembly (this file proves only the bridges; every imported theorem is used as stated):
1. `pieri310` : Ellis (3.10) in the elimination's vocabulary `OddLRElimination.Pieri310 N`
   (row sets `stripRows`, sign Σ_{a∈I} `belowRows λ a`), for EVERY N, derived from the
   unconditional `OddLRVerticalPieri.vertical_pieri` (vertical strips over `DegreeShape`,
   sign `stripBelow`).  Bridges: `column k = columnShape k`; `belowCount = belowRows`; the
   bijection I ↦ `addStrip λ k I`, μ ↦ rows of μ/λ between `stripRows λ k` and the vertical
   strips of size k.
2. `sp_eq_schur`, `eliminationC` : composition with `OddLRElimination.sp_eq_schur_of_pieri310`;
   `eliminationC n` is literally `OddLREKIdentification.EliminationC n` (the bridge
   `toExponent n λ = ofYoung λ` holds by `rfl`, same row bound n+2, same carrier `sp (n+2)`).
3. `thm38` : π_{n+2} s^K_λ = s^p_λ = s^s_λ for every λ with at most N = n+2 rows, and
   `thm38_tall` : for λ with more than N rows, π_N s^K_λ = s^p_λ = 0 (Remark 3.4:
   "s_λ = 0 in OΛ_n if and only if λ has height greater than n"; the zero half is proved,
   the carrier `OddSymmetrizer.schur` has no s^s index for such λ).
-/
namespace OddMath.Frontier.OddLRThm38
open scoped BigOperators
open OddMath.SkewPolynomial
open OddLRVerticalPieri (Vertical belowCount stripBelow)
open OddLRElimination (belowRows rowInc stripRows addStrip)
noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## 1. Vocabulary bridges -/

/-- The one-column diagram of the vertical Pieri rule is the literal (1^k) of `TableauExtremal`. -/
theorem column_eq_columnShape (k : ℕ) :
    OddLRVerticalPieri.column k = TableauExtremal.columnShape k := by
  apply YoungDiagram.ext
  ext ⟨a, b⟩
  change (a, b) ∈ OddLRVerticalPieri.column k ↔ (a, b) ∈ TableauExtremal.columnShape k
  rw [OddLRVerticalPieri.mem_column, TableauExtremal.mem_columnShape]
  exact and_comm

/-- The two transcriptions of |i/λ| agree: boxes of λ strictly below row a. -/
theorem belowCount_eq_belowRows (lam : YoungDiagram) (a : ℕ) :
    belowCount lam a = belowRows lam a := by
  unfold OddLRVerticalPieri.belowCount OddLRElimination.belowRows
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range (lam.colLen 0))]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Finset.filter_filter]
    split_ifs with hab
    · rw [lam.rowLen_eq_card]
      congr 1
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, YoungDiagram.mem_row_iff, YoungDiagram.mem_cells]
      constructor
      · rintro ⟨hq, _, h⟩; exact ⟨hq, h⟩
      · rintro ⟨hq, h⟩; exact ⟨hq, by omega, h⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨i, j⟩ _ ⟨h1, h2⟩
      simp only at h1 h2
      exact hab (h2 ▸ h1)
  · rintro ⟨i, j⟩ hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, YoungDiagram.mem_cells] at hq
    simp only [Finset.coe_range, Set.mem_Iio]
    rw [← YoungDiagram.mem_iff_lt_colLen]
    exact lam.up_left_mem le_rfl (Nat.zero_le _) hq.1

/-- The rows of μ/λ. -/
def rowsOf (lam mu : YoungDiagram) : Finset ℕ := (mu.cells \ lam.cells).image Prod.fst

theorem fst_injOn {lam mu : YoungDiagram} (h : Vertical lam mu) :
    Set.InjOn Prod.fst (↑(mu.cells \ lam.cells) : Set (ℕ × ℕ)) :=
  fun p hp q hq he => h.2 p hp q hq he

theorem card_rowsOf {lam mu : YoungDiagram} (h : Vertical lam mu) :
    (rowsOf lam mu).card = (mu.cells \ lam.cells).card :=
  Finset.card_image_of_injOn (fst_injOn h)

/-- Over a vertical strip, μ has row lengths `rowInc λ (rows of μ/λ)`. -/
theorem rowLen_of_vertical {lam mu : YoungDiagram} (h : Vertical lam mu) (a : ℕ) :
    mu.rowLen a = rowInc lam (rowsOf lam mu) a := by
  unfold OddLRElimination.rowInc
  have hle : lam.rowLen a ≤ mu.rowLen a := by
    by_contra hn
    push_neg at hn
    have h1 : (a, mu.rowLen a) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr hn
    have h2 : (a, mu.rowLen a) ∈ mu :=
      (YoungDiagram.mem_cells _).mp (h.1 ((YoungDiagram.mem_cells _).mpr h1))
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2
    omega
  have hmem : a ∈ rowsOf lam mu ↔ lam.rowLen a < mu.rowLen a := by
    unfold rowsOf
    simp only [Finset.mem_image, Finset.mem_sdiff, YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨i, j⟩, ⟨h1, h2⟩, rfl⟩
      rw [YoungDiagram.mem_iff_lt_rowLen] at h1 h2
      simp only
      omega
    · intro hlt
      refine ⟨(a, lam.rowLen a), ⟨?_, ?_⟩, rfl⟩
      · rw [YoungDiagram.mem_iff_lt_rowLen]; exact hlt
      · rw [YoungDiagram.mem_iff_lt_rowLen]; exact lt_irrefl _
  have hup : mu.rowLen a ≤ lam.rowLen a + 1 := by
    by_contra hn
    push_neg at hn
    have p1 : (a, lam.rowLen a) ∈ mu.cells \ lam.cells := by
      simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
      omega
    have p2 : (a, lam.rowLen a + 1) ∈ mu.cells \ lam.cells := by
      simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
      omega
    have := h.2 _ p1 _ p2 rfl
    simp at this
  split_ifs with ha
  · have := hmem.mp ha; omega
  · have := mt hmem.mpr ha; omega

/-- Over a vertical strip the printed exponent is the row-set exponent of the elimination. -/
theorem stripBelow_of_vertical {lam mu : YoungDiagram} (h : Vertical lam mu) :
    stripBelow lam mu = ∑ a ∈ rowsOf lam mu, belowRows lam a := by
  unfold OddLRVerticalPieri.stripBelow rowsOf
  rw [Finset.sum_image (fun p hp q hq he => fst_injOn h hp hq he)]
  exact Finset.sum_congr rfl (fun p _ => belowCount_eq_belowRows lam p.1)

theorem diagram_ext_rowLen {mu nu : YoungDiagram} (h : ∀ a, mu.rowLen a = nu.rowLen a) :
    mu = nu := by
  apply YoungDiagram.ext
  ext ⟨a, b⟩
  change (a, b) ∈ mu ↔ (a, b) ∈ nu
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, h a]

/-! ## 2. `addStrip` on the index set `stripRows` -/

section addStrip
variable {lam : YoungDiagram} {k : ℕ} {I : Finset ℕ}

theorem rowLen_addStrip (hI : I ∈ stripRows lam k) (a : ℕ) :
    (addStrip lam k I).rowLen a = rowInc lam I a := by
  apply eq_of_forall_lt_iff
  intro b
  rw [← YoungDiagram.mem_iff_lt_rowLen, OddLRElimination.mem_addStrip _ _ hI]

theorem mem_addStrip_sdiff (hI : I ∈ stripRows lam k) (p : ℕ × ℕ) :
    p ∈ (addStrip lam k I).cells \ lam.cells ↔ p.1 ∈ I ∧ p.2 = lam.rowLen p.1 := by
  obtain ⟨a, b⟩ := p
  simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, OddLRElimination.mem_addStrip _ _ hI,
    YoungDiagram.mem_iff_lt_rowLen, OddLRElimination.rowInc]
  by_cases ha : a ∈ I
  · simp only [ha, if_true, true_and]; omega
  · simp only [ha, if_false, false_and, iff_false, add_zero]; omega

theorem subset_addStrip (hI : I ∈ stripRows lam k) : lam.cells ⊆ (addStrip lam k I).cells := by
  rintro ⟨a, b⟩ hp
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hp ⊢
  rw [rowLen_addStrip hI]
  unfold OddLRElimination.rowInc
  omega

theorem vertical_addStrip (hI : I ∈ stripRows lam k) : Vertical lam (addStrip lam k I) := by
  refine ⟨subset_addStrip hI, ?_⟩
  intro p hp q hq he
  rw [mem_addStrip_sdiff hI] at hp hq
  exact Prod.ext he (by rw [hp.2, hq.2, he])

theorem rowsOf_addStrip (hI : I ∈ stripRows lam k) : rowsOf lam (addStrip lam k I) = I := by
  ext a
  unfold rowsOf
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ((mem_addStrip_sdiff hI p).mp hp).1
  · intro ha
    exact ⟨(a, lam.rowLen a), (mem_addStrip_sdiff hI _).mpr ⟨ha, rfl⟩, rfl⟩

theorem card_stripRows (hI : I ∈ stripRows lam k) : I.card = k := by
  simp only [OddLRElimination.stripRows, Finset.mem_filter] at hI
  exact hI.2.1

theorem card_addStrip (hI : I ∈ stripRows lam k) : (addStrip lam k I).card = lam.card + k := by
  have h1 := Finset.card_sdiff_add_card_eq_card (subset_addStrip hI)
  rw [← card_rowsOf (vertical_addStrip hI), rowsOf_addStrip hI, card_stripRows hI] at h1
  change (addStrip lam k I).cells.card = lam.cells.card + k
  omega

end addStrip

/-- The rows of a vertical k-strip form an index of `stripRows`. -/
theorem rowsOf_mem {lam mu : YoungDiagram} {k : ℕ} (h : Vertical lam mu)
    (hc : mu.card = lam.card + k) : rowsOf lam mu ∈ stripRows lam k := by
  apply OddLRElimination.stripRows_complete
  · rw [card_rowsOf h, Finset.card_sdiff h.1]
    change mu.cells.card = lam.cells.card + k at hc
    omega
  · have : rowInc lam (rowsOf lam mu) = mu.rowLen := funext (fun a => (rowLen_of_vertical h a).symm)
    rw [this]
    exact fun a b hab => mu.rowLen_anti a b hab

theorem addStrip_rowsOf {lam mu : YoungDiagram} {k : ℕ} (h : Vertical lam mu)
    (hc : mu.card = lam.card + k) : addStrip lam k (rowsOf lam mu) = mu := by
  apply diagram_ext_rowLen
  intro a
  rw [rowLen_addStrip (rowsOf_mem h hc), rowLen_of_vertical h]

/-! ## 3. Ellis (3.10) in the elimination's vocabulary, unconditionally -/

/-- **Ellis (3.10)**, unconditional, in the exact form `OddLRElimination.Pieri310 N` required by
the elimination, for every number of variables N:
s^p_λ s^p_{(1^k)} = Σ_{I ∈ stripRows λ k} (-1)^{Σ_{a∈I} |(a+1)/λ|} s^p_{λ + strip(I)}.
Derived from `OddLRVerticalPieri.vertical_pieri` by the vertical-strip ↔ row-set
bijection above; signs agree term by term (`stripBelow_of_vertical`). -/
theorem pieri310 (N : ℕ) : OddLRElimination.Pieri310 N := by
  intro lam k
  letI := DegreeShapes.degreeFintype (lam.card + k)
  have hv := OddLRVerticalPieri.vertical_pieri N lam k
  rw [column_eq_columnShape] at hv
  rw [hv, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij'
    (fun I hI => (⟨addStrip lam k I, card_addStrip hI⟩ : DegreeShapes.DegreeShape (lam.card + k)))
    (fun mu _ => rowsOf lam mu.val) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, vertical_addStrip hI⟩
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    exact rowsOf_mem hmu.2 mu.property
  · intro I hI
    exact rowsOf_addStrip hI
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    exact Subtype.ext (addStrip_rowsOf hmu.2 mu.property)
  · intro I hI
    change _ = (-1 : ℤ) ^ stripBelow lam (addStrip lam k I) •
      CompleteTableauExpansion.sp N (addStrip lam k I)
    rw [stripBelow_of_vertical (vertical_addStrip hI), rowsOf_addStrip hI]

/-- The bounded row-set hypothesis of the elimination, discharged. -/
theorem pieri310Bounded (n : ℕ) : OddLRElimination.Pieri310Bounded n :=
  OddLRElimination.pieri310_bounded n (pieri310 (n+2))

/-! ## 4. s^p = s^s and the identification hypothesis -/

/-- s^p = s^s on the elimination's own carrier (every padded partition, N = n+2). -/
theorem sp_eq_schur (n : ℕ) (α : OddSymmetrizer.PartitionExponent n) :
    CompleteTableauExpansion.sp (n+2) (OddLRElimination.toYoung α) = OddSymmetrizer.schur n α :=
  OddLRElimination.sp_eq_schur_of_pieri310 n (pieri310 (n+2)) α

/-- The two row-length bridges coincide definitionally. -/
theorem toExponent_eq_ofYoung (n : ℕ) (lam : YoungDiagram) :
    OddLREKIdentification.toExponent n lam = OddLRElimination.ofYoung (n := n) lam := rfl

/-- `EliminationC n`, exactly the hypothesis of `OddLREKIdentification.thm38_conditional`, discharged: sp (n+2) λ = schur n (toExponent n λ) for every λ with ≤ n+2 rows. -/
theorem eliminationC (n : ℕ) : OddLREKIdentification.EliminationC n := by
  intro lam hl
  rw [toExponent_eq_ofYoung]
  exact OddLRElimination.sp_eq_schur_diagram_of_pieri310 n (pieri310 (n+2)) lam hl

/-! ## 5. Theorem 3.8 -/

/-- **Ellis, Theorem 3.8, (3.9)** (arXiv:1111.3932v1 §3.2): "The three notions of odd Schur
function all coincide: for any partition λ, s^K_λ = s^p_λ = s^s_λ."

On the actual carriers, for every partition (Young diagram) λ and every N = n+2 ≥ ℓ(λ):
`piN N (sK λ) = sp N λ` (s^K projected to N odd variables equals the plactic s^p of (3.4),
sign (-1)^{dN(λ)+N(λ)}) and `sp N λ = schur n (toExponent n λ)` (the odd-symmetrized s^s of
EKL).  No hypothesis beyond the row bound, which is where s^s has an index. -/
theorem thm38 (n : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ n + 2) :
    OddLREKIdentification.piN (n+2) (OddLREKIdentification.sK lam) =
        CompleteTableauExpansion.sp (n+2) lam ∧
      CompleteTableauExpansion.sp (n+2) lam =
        OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam) :=
  OddLREKIdentification.thm38_conditional n (eliminationC n) lam hl

/-- (3.9) read end to end: π_{n+2} s^K_λ = s^s_λ for every λ with at most n+2 rows. -/
theorem sK_eq_schur (n : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ n + 2) :
    OddLREKIdentification.piN (n+2) (OddLREKIdentification.sK lam) =
      OddSymmetrizer.schur n (OddLREKIdentification.toExponent n lam) :=
  (thm38 n lam hl).1.trans (thm38 n lam hl).2

/-- Remark 3.4 (zero half) on the actual carriers: for λ of height greater than N,
π_N s^K_λ = s^p_λ = 0 in N odd variables, for every N. -/
theorem thm38_tall (N : ℕ) (lam : YoungDiagram) (h : N < lam.colLen 0) :
    OddLREKIdentification.piN N (OddLREKIdentification.sK lam) = 0 ∧
      CompleteTableauExpansion.sp N lam = 0 := by
  have hs : CompleteTableauExpansion.sp N lam = 0 :=
    OddLRElimination.sp_tall N lam (YoungDiagram.mem_iff_lt_colLen.mpr h)
  exact ⟨(OddLREKIdentification.piN_sK N lam).trans hs, hs⟩

/-- π_N s^K_λ = s^p_λ for every λ and every N (no row bound). -/
theorem sK_eq_sp (N : ℕ) (lam : YoungDiagram) :
    OddLREKIdentification.piN N (OddLREKIdentification.sK lam) =
      CompleteTableauExpansion.sp N lam :=
  OddLREKIdentification.piN_sK N lam

end
end OddMath.Frontier.OddLRThm38
