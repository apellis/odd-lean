import OddMath.Frontier.EKProp310Controls

/-!
# EK1107.5610v2 §3.3, Proposition 3.10 (printed p29): the e-side characterisation of s_λ

Source (frozen source excerpt, PAGE 28–29): after Corollary 3.9, the two
properties preceding (3.12) characterise `s_λ` in the h-basis; Proposition 3.10 is the
e-side analogue:

  Define `s'_λ` by `s'_(1ⁿ) = e_n` and
  (1) `(s'_λ, e_μ) = 0` if `μ > λᵀ` (lexicographic order);
  (2) `s'_λ = e_{λᵀ} + Σ_{μ > λᵀ} b_μ e_μ` for certain integers `b_μ`.
  Then `s'_λ = (-1)^{ℓ(w_λ) + C(λᵀ,2)} s_λ`.

Objects (all actual existing objects, nothing re-modelled):
* `schur d λ = KostkaModuleInversion.recover d (degreeHBasis d)`: the source `s_λ` defined
  by (3.6) with the literal odd Kostka numbers (3.7). This is the SAME definition as
  `EKSchurOrthonormal.schur`.
* `e_μ = ePartition μ = e_{μ₁} e_{μ₂} ⋯` (`degreeEBasis`), pairing `quotientPairing` on Q.
* "lexicographic order": `LexLT μ ν :⇔ μ.rowLens < ν.rowLens` (List lex on the
  weakly decreasing row lists; the order used by `EKSemiorthogonality`).
* `ℓ(w_λ)`: `EKSemiorthogonality.ell λ`, the NE-pair count, i.e. exactly the sign of the
  existing `EKDualBases.triangularMatrix_diag` / source (2.21)
  `(h_λ, e_{λᵀ}) = (-1)^{ℓ(w_λ)}` (`EKSemiorthogonality.proposition_2_14_diagonal`).
* `C(λᵀ,2) = transposeChoose λ = Σ_j C(λᵀ_j,2)` (same definition as in `EKSchurOrthonormal`).

Main results:
* `proposition_3_10 d h311 λ`: for every degree d, ASSUMING exactly (3.11) in degree d
  (`Identity311 d`, the `EKSchurOrthonormal.corollary_3_9` statement), there is exactly one
  `s'_λ` with (1) and (2), and it equals `(-1)^{ℓ(w_λ)+C(λᵀ,2)} • s_λ`.
* `proposition_3_10_iff_identity311`: the hypothesis is SHARP: "`sgn(λ)•s_λ` satisfies
  (1),(2) for every λ ⊢ d" is equivalent to (3.11) in degree d.
* `proposition_3_10_le_four`: unconditional for d ≤ 4 ((3.11) discharged directly by exact
  computation: hand `s_λ` families checked against (3.6) with the kernel odd-Kostka tables of
  `EKProp310Controls`, then their exact Gram matrices from the kernel M′ = (h,h) tables).
* Composition: the unconditional all-d theorem is the term
  `proposition_3_10 d (EKSchurOrthonormal.corollary_3_9 d h39)` with `h39 : Identity39 d` from
  the `EKKostkaValues` (3.9) theorem (assembled in `EKClosureComposition`); this module re-proves neither.
* By-product `eAbove_restricted_nondeg` (the E-half of the pairing nondegeneracy that the
  source attributes to Lemma 2.15), under the same (3.11) hypothesis.

Route (differs from the source proof, which cites Lemma 2.15 whose middle complement
equality is refuted by the existing `EKRestrictedPairing`): no Lemma 2.15 is used.
* Unconditional in every degree: dominance ⇒ lex, dominance reverses under transpose,
  hence (3.6) + Prop 2.14 vanishing give property (1) for `s_λ`, and (2.21) gives
  `(s_λ, e_{λᵀ}) = (-1)^{ℓ(w_λ)}`.
* With (3.11): the Schur expansion `x = Σ_κ ε_κ (s_κ, x) s_κ` and a triangular induction
  give `s_λ - sgn(λ) e_{λᵀ} ∈ span{e_μ : μ > λᵀ}` (property (2) for `sgn(λ) s_λ`);
  uniqueness: a difference `y ∈ span{e_μ : μ > λᵀ}` orthogonal to all those `e_μ` has
  `(s_κ, y) = 0` for every κ, hence `y = 0`.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace OddMath.Frontier.EKProp310
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance
open EKPartitionSpanning (hPartition ePartition)
open EKProp310Controls (transposeChoose)
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Orders: lexicographic and dominance -/

/-- Source "lexicographic order" on partitions: row-length lists compared lexicographically. -/
def LexLT (μ ν : YoungDiagram) : Prop := μ.rowLens < ν.rowLens

/-- Dominance `μ ⊴ ν` by the existing row-prefix cell counts. -/
def Dom (μ ν : YoungDiagram) : Prop := ∀ k, shapePrefix μ k ≤ shapePrefix ν k

theorem dom_trans {a b c : YoungDiagram} (h1 : Dom a b) (h2 : Dom b c) : Dom a c :=
  fun k => (h1 k).trans (h2 k)

theorem dom_antisymm {a b : YoungDiagram} (h1 : Dom a b) (h2 : Dom b a) : a = b :=
  SignedKostkaInvertibility.shapePrefix_injective (funext fun k => le_antisymm (h1 k) (h2 k))

theorem dom_of_kostka_ne_zero {lam mu : YoungDiagram} (h : signedKostka lam mu ≠ 0) : Dom mu lam := by
  intro k
  by_contra hk
  exact h (signedKostka_zero_of_prefix lam mu ⟨k, by omega⟩)

/-- Converse of `EKSemiorthogonality.lex_first_larger`. -/
theorem lex_of_first_larger : ∀ {L M : List ℕ} (_hpos : ∀ a ∈ L, 0 < a) (j : ℕ),
    (∀ k < j, L[k]?.getD 0 = M[k]?.getD 0) → L[j]?.getD 0 < M[j]?.getD 0 →
      List.Lex (· < ·) L M
  | [], [], _, j, _, hj => by simp at hj
  | [], _ :: _, _, _, _, _ => List.Lex.nil
  | a :: L, [], hpos, j, hprev, hj => by
      exfalso
      cases j with
      | zero => simp at hj
      | succ j =>
        have h0 := hprev 0 (by omega)
        have ha := hpos a (by simp)
        simp at h0
        omega
  | a :: L, b :: M, hpos, j, hprev, hj => by
      cases j with
      | zero => exact List.Lex.rel (by simpa using hj)
      | succ j =>
        have h0 : a = b := by simpa using hprev 0 (by omega)
        subst h0
        exact List.Lex.cons (lex_of_first_larger (fun x hx => hpos x (by simp [hx])) j
          (fun k hk => by simpa using hprev (k+1) (by omega)) (by simpa using hj))

theorem shapePrefix_zero (μ : YoungDiagram) : shapePrefix μ 0 = 0 := by
  simp [shapePrefix]

theorem shapePrefix_eq_of_rowLen {μ ν : YoungDiagram} : ∀ j,
    (∀ k < j, μ.rowLen k = ν.rowLen k) → shapePrefix μ j = shapePrefix ν j
  | 0, _ => by rw [shapePrefix_zero, shapePrefix_zero]
  | j+1, h => by
    rw [SignedKostkaInvertibility.shapePrefix_succ, SignedKostkaInvertibility.shapePrefix_succ,
      shapePrefix_eq_of_rowLen j (fun k hk => h k (by omega)), h j (by omega)]

/-- D1: dominance implies lexicographic `≤`. -/
theorem lex_le_of_dom {μ ν : YoungDiagram} (h : Dom μ ν) : μ = ν ∨ LexLT μ ν := by
  by_cases he : μ = ν
  · exact Or.inl he
  right
  have hex : ∃ j, μ.rowLen j ≠ ν.rowLen j := by
    by_contra hc
    push_neg at hc
    apply he
    apply YoungDiagram.ext
    ext ⟨r, c⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hc]
  classical
  let j := Nat.find hex
  have hj : μ.rowLen j ≠ ν.rowLen j := Nat.find_spec hex
  have hprev : ∀ k < j, μ.rowLen k = ν.rowLen k := fun k hk => by
    have := Nat.find_min hex hk
    simpa using this
  have hp := h (j+1)
  rw [SignedKostkaInvertibility.shapePrefix_succ, SignedKostkaInvertibility.shapePrefix_succ,
    shapePrefix_eq_of_rowLen j hprev] at hp
  have hlt : μ.rowLen j < ν.rowLen j := by omega
  show List.Lex (· < ·) μ.rowLens ν.rowLens
  apply lex_of_first_larger (μ.pos_of_mem_rowLens) j
  · intro k hk
    rw [EKSemiorthogonality.rowLens_getD, EKSemiorthogonality.rowLens_getD]
    exact hprev k hk
  · rw [EKSemiorthogonality.rowLens_getD, EKSemiorthogonality.rowLens_getD]
    exact hlt

/-- Column-prefix cell counts. -/
def colPrefix (μ : YoungDiagram) (k : ℕ) : ℕ := (μ.cells.filter (fun p => p.2 < k)).card

theorem shapePrefix_transpose (μ : YoungDiagram) (k : ℕ) :
    shapePrefix μ.transpose k = colPrefix μ k := by
  unfold shapePrefix colPrefix
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    simp only [Finset.mem_filter, YoungDiagram.mem_cells] at hp ⊢
    exact ⟨YoungDiagram.mem_transpose.mp hp.1, by simpa using hp.2⟩
  · intro a _ b _ h
    simpa using h
  · intro p hp
    simp only [Finset.mem_filter, YoungDiagram.mem_cells] at hp
    refine ⟨p.swap, ?_, by simp⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨YoungDiagram.mem_transpose.mpr (by simpa using hp.1), by simpa using hp.2⟩

private theorem rect_card (μ : YoungDiagram) (k : ℕ) :
    (μ.cells.filter (fun p => p.1 < μ.colLen k ∧ p.2 < k)).card = μ.colLen k * k := by
  have : μ.cells.filter (fun p => p.1 < μ.colLen k ∧ p.2 < k) =
      Finset.range (μ.colLen k) ×ˢ Finset.range k := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      have hk : (i, k) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr h1
      exact μ.up_left_mem le_rfl (Nat.le_of_lt h2) hk
  rw [this, Finset.card_product, Finset.card_range, Finset.card_range]

private theorem rect_card_le (μ : YoungDiagram) (r k : ℕ) :
    (μ.cells.filter (fun p => p.1 < r ∧ p.2 < k)).card ≤ r * k := by
  calc (μ.cells.filter (fun p => p.1 < r ∧ p.2 < k)).card
      ≤ (Finset.range r ×ˢ Finset.range k).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp
        simp [hp.2.1, hp.2.2]
    _ = r * k := by simp

/-- D2: dominance reverses under transposition (equal sizes). -/
theorem dom_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card) (h : Dom μ ν) :
    Dom ν.transpose μ.transpose := by
  intro k
  rw [shapePrefix_transpose, shapePrefix_transpose]
  set r := μ.colLen k
  -- cells of μ in columns ≥ k all lie in rows < r
  have hA : (μ.cells.filter (fun p => ¬ p.2 < k)) =
      μ.cells.filter (fun p => p.1 < r ∧ ¬ p.2 < k) := by
    apply Finset.filter_congr
    intro p hp
    simp only [YoungDiagram.mem_cells] at hp
    constructor
    · intro hk
      refine ⟨?_, hk⟩
      have : (p.1, k) ∈ μ := μ.up_left_mem le_rfl (by omega) hp
      exact YoungDiagram.mem_iff_lt_colLen.mp this
    · exact fun h => h.2
  have hsplit (τ : YoungDiagram) : shapePrefix τ r =
      (τ.cells.filter (fun p => p.1 < r ∧ ¬ p.2 < k)).card +
      (τ.cells.filter (fun p => p.1 < r ∧ p.2 < k)).card := by
    unfold shapePrefix
    rw [← Finset.filter_card_add_filter_neg_card_eq_card (fun p : ℕ × ℕ => p.2 < k),
      Finset.filter_filter, Finset.filter_filter, add_comm]
  have hμ := hsplit μ
  have hν := hsplit ν
  rw [rect_card μ k] at hμ
  have hrk : μ.colLen k * k = r * k := rfl
  have hν2 := rect_card_le ν r k
  have hsub : (ν.cells.filter (fun p => p.1 < r ∧ ¬ p.2 < k)).card ≤
      (ν.cells.filter (fun p => ¬ p.2 < k)).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have hdom := h r
  have hμA : (μ.cells.filter (fun p => ¬ p.2 < k)).card ≤
      (ν.cells.filter (fun p => ¬ p.2 < k)).card := by
    rw [hA]; omega
  have htμ := Finset.filter_card_add_filter_neg_card_eq_card (s := μ.cells) (fun p : ℕ × ℕ => p.2 < k)
  have htν := Finset.filter_card_add_filter_neg_card_eq_card (s := ν.cells) (fun p : ℕ × ℕ => p.2 < k)
  unfold colPrefix
  change _ = μ.card at htμ
  change _ = ν.card at htν
  omega


/-! ## Degree-d algebra -/


theorem lexLT_trichotomy (a b : YoungDiagram) : LexLT a b ∨ a = b ∨ LexLT b a := by
  rcases lt_trichotomy a.rowLens b.rowLens with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (YoungDiagram.equivListRowLens.injective (Subtype.ext h)))
  · exact Or.inr (Or.inr h)

@[simp] theorem transposeShape_val (d : ℕ) (lam : DegreeShape d) :
    (transposeShape d lam).val = lam.val.transpose := rfl

theorem pair_h_e_vanish (ν μ : YoungDiagram) (h : LexLT ν.transpose μ) :
    quotientPairing (hPartition ν) (ePartition μ) = 0 :=
  (EKSemiorthogonality.proposition_2_14_vanishing ν μ.rowLens μ.pos_of_mem_rowLens h).1

theorem pair_h_e_diag (ν : YoungDiagram) :
    quotientPairing (hPartition ν) (ePartition ν.transpose) = (-1 : ℤ) ^ EKSemiorthogonality.ell ν :=
  EKSemiorthogonality.proposition_2_14_diagonal ν

def schur (d : ℕ) : DegreeShape d → degreePiece d :=
  KostkaModuleInversion.recover d (degreeHBasis d)

theorem schur_defining (d : ℕ) (μ : DegreeShape d) :
    degreeHBasis d μ = ∑ lam, signedKostka lam.val μ.val • schur d lam :=
  (congrFun (KostkaModuleInversion.rightInverse d (⇑(degreeHBasis d))) μ).symm

def Up (d : ℕ) (lam : DegreeShape d) : Submodule ℤ (degreePiece d) :=
  Submodule.span ℤ (degreeHBasis d '' {ν | Dom lam.val ν.val})

def UpS (d : ℕ) (lam : DegreeShape d) : Submodule ℤ (degreePiece d) :=
  Submodule.span ℤ (degreeHBasis d '' {ν | Dom lam.val ν.val ∧ ν ≠ lam})

def Above (d : ℕ) (a b : DegreeShape d) : Prop := Dom b.val a.val ∧ a ≠ b

instance (d : ℕ) : IsTrans (DegreeShape d) (Above d) :=
  ⟨fun a b c h1 h2 => ⟨dom_trans h2.1 h1.1, by
    rintro rfl
    exact h1.2 (Subtype.ext (dom_antisymm h1.1 h2.1)).symm⟩⟩

instance (d : ℕ) : IsIrrefl (DegreeShape d) (Above d) := ⟨fun _ h => h.2 rfl⟩

theorem above_wf (d : ℕ) : WellFounded (Above d) := Finite.wellFounded_of_trans_of_irrefl _

theorem up_of_upS {d : ℕ} {lam : DegreeShape d} (h : schur d lam - degreeHBasis d lam ∈ UpS d lam) :
    schur d lam ∈ Up d lam := by
  have h1 : UpS d lam ≤ Up d lam := Submodule.span_mono (Set.image_subset _ (fun ν hν => hν.1))
  have h2 : degreeHBasis d lam ∈ Up d lam := Submodule.subset_span ⟨lam, fun _ => le_rfl, rfl⟩
  have := Submodule.add_mem _ (h1 h) h2
  simpa using this

/-- (3.6) inverted: `s_λ - h_λ` lies in the span of `h_ν`, `ν` strictly dominating `λ`. -/
theorem schur_sub_mem_upS (d : ℕ) (lam : DegreeShape d) :
    schur d lam - degreeHBasis d lam ∈ UpS d lam := by
  induction lam using (above_wf d).induction with
  | _ lam ih =>
  have hdef := schur_defining d lam
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ lam), signedKostka_diag, one_smul] at hdef
  have hs : schur d lam - degreeHBasis d lam =
      -(∑ κ ∈ Finset.univ.erase lam, signedKostka κ.val lam.val • schur d κ) := by
    rw [hdef, sub_add_eq_sub_sub, sub_self, zero_sub]
  rw [hs]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun κ hκ => ?_)
  by_cases hK : signedKostka κ.val lam.val = 0
  · rw [hK, zero_smul]; exact Submodule.zero_mem _
  have hdom : Dom lam.val κ.val := dom_of_kostka_ne_zero hK
  have hne : κ ≠ lam := Finset.ne_of_mem_erase hκ
  have hup := up_of_upS (ih κ ⟨hdom, hne⟩)
  refine Submodule.smul_mem _ _ ((Submodule.span_mono ?_) hup)
  rintro _ ⟨ν, hν, rfl⟩
  refine ⟨ν, ⟨dom_trans hdom hν, ?_⟩, rfl⟩
  rintro rfl
  exact hne (Subtype.ext (dom_antisymm hν hdom))

/-- Property (1) for `s_λ`: `(s_λ, e_μ) = 0` for `μ > λᵀ` (lex). -/
theorem pair_schur_e_vanish (d : ℕ) (lam μ : DegreeShape d) (h : LexLT lam.val.transpose μ.val) :
    quotientPairing (schur d lam : Q) (ePartition μ.val) = 0 := by
  have hle : Up d lam ≤ LinearMap.ker (pairingMap d (degreeEBasis d μ)) := by
    rw [Up, Submodule.span_le]
    rintro _ ⟨ν, hν, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, pairingMap_apply, degreeHBasis_apply,
      degreeEBasis_apply]
    apply pair_h_e_vanish
    have ht := dom_transpose (lam.property.trans ν.property.symm) hν
    rcases lex_le_of_dom ht with he | hl
    · rw [he]; exact h
    · exact lt_trans hl h
  have := hle (up_of_upS (schur_sub_mem_upS d lam))
  simpa [pairingMap_apply] using this

/-- Source (2.21) transported to `s_λ`: `(s_λ, e_{λᵀ}) = (-1)^{ℓ(w_λ)}`. -/
theorem pair_schur_e_diag (d : ℕ) (lam : DegreeShape d) :
    quotientPairing (schur d lam : Q) (ePartition lam.val.transpose) =
      (-1 : ℤ) ^ EKSemiorthogonality.ell lam.val := by
  have hle : UpS d lam ≤ LinearMap.ker (pairingMap d (degreeEBasis d (transposeShape d lam))) := by
    rw [UpS, Submodule.span_le]
    rintro _ ⟨ν, ⟨hν, hne⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, pairingMap_apply, degreeHBasis_apply,
      degreeEBasis_apply, transposeShape_val]
    apply pair_h_e_vanish
    have ht := dom_transpose (lam.property.trans ν.property.symm) hν
    rcases lex_le_of_dom ht with he | hl
    · exact absurd (Subtype.ext (YoungDiagram.transpose_eq_iff.mp he)) hne
    · exact hl
  have h1 := hle (schur_sub_mem_upS d lam)
  simp only [LinearMap.mem_ker, pairingMap_apply, Submodule.coe_sub, map_sub,
    LinearMap.sub_apply, degreeHBasis_apply, degreeEBasis_apply, transposeShape_val] at h1
  rw [← pair_h_e_diag]
  omega

/-- Hypothesis: exactly (3.11) in degree `d`. -/
def Identity311 (d : ℕ) : Prop :=
  ∀ lam μ : DegreeShape d, quotientPairing (schur d lam : Q) (schur d μ : Q) =
    if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0

theorem sign_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem schur_span (d : ℕ) : Submodule.span ℤ (Set.range (schur d)) = ⊤ := by
  rw [eq_top_iff, ← (degreeHBasis d).span_eq, Submodule.span_le]
  rintro _ ⟨μ, rfl⟩
  rw [SetLike.mem_coe, schur_defining]
  exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ, rfl⟩)

theorem expansion (d : ℕ) (h311 : Identity311 d) (x : degreePiece d) :
    x = ∑ κ, ((-1 : ℤ) ^ transposeChoose κ.val * quotientPairing (schur d κ : Q) (x : Q)) •
      schur d κ := by
  have hx : x ∈ Submodule.span ℤ (Set.range (schur d)) := by rw [schur_span]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  have hcoef (κ : DegreeShape d) :
      (-1 : ℤ) ^ transposeChoose κ.val * quotientPairing (schur d κ : Q) (x : Q) = c κ := by
    have h' := h311
    unfold Identity311 at h'
    rw [← hc, Submodule.coe_sum, map_sum]
    simp only [Submodule.coe_smul, map_zsmul, h', smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rw [mul_left_comm, sign_mul_self, mul_one]
  simp only [hcoef]
  exact hc.symm

def EAbove (d : ℕ) (κ : YoungDiagram) : Submodule ℤ (degreePiece d) :=
  Submodule.span ℤ (degreeEBasis d '' {μ | LexLT κ μ.val})

def TAbove (d : ℕ) (a b : DegreeShape d) : Prop := LexLT b.val.transpose a.val.transpose

instance (d : ℕ) : IsTrans (DegreeShape d) (TAbove d) := ⟨fun _ _ _ h1 h2 => lt_trans h2 h1⟩
instance (d : ℕ) : IsIrrefl (DegreeShape d) (TAbove d) := ⟨fun _ h => lt_irrefl _ h⟩
theorem tabove_wf (d : ℕ) : WellFounded (TAbove d) := Finite.wellFounded_of_trans_of_irrefl _

/-- The Proposition 3.10 sign `(-1)^{ℓ(w_λ) + C(λᵀ,2)}`. -/
def sgn (lam : YoungDiagram) : ℤ := (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + transposeChoose lam)

theorem sgn_sq (lam : YoungDiagram) : sgn lam * sgn lam = 1 := sign_mul_self _

theorem eAbove_mono (d : ℕ) {a b : YoungDiagram} (h : LexLT a b) : EAbove d b ≤ EAbove d a :=
  Submodule.span_mono (Set.image_subset _ (fun _ hμ => lt_trans h hμ))

/-- Triangular inversion: `s_λ - sgn(λ) e_{λᵀ} ∈ span{e_μ : μ > λᵀ}`. -/
theorem schur_sub_e_mem (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d) :
    schur d lam - sgn lam.val • degreeEBasis d (transposeShape d lam) ∈
      EAbove d lam.val.transpose := by
  induction lam using (tabove_wf d).induction with
  | _ lam ih =>
  have hx := expansion d h311 (degreeEBasis d (transposeShape d lam))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ lam)] at hx
  have hc : (-1 : ℤ) ^ transposeChoose lam.val *
      quotientPairing (schur d lam : Q) ((degreeEBasis d (transposeShape d lam)) : Q) = sgn lam.val := by
    rw [degreeEBasis_apply, transposeShape_val, pair_schur_e_diag, sgn, pow_add, mul_comm]
  rw [hc] at hx
  set rest := ∑ κ ∈ Finset.univ.erase lam, ((-1 : ℤ) ^ transposeChoose κ.val *
      quotientPairing (schur d κ : Q) ((degreeEBasis d (transposeShape d lam)) : Q)) • schur d κ
    with hrest_def
  have hrest : rest ∈ EAbove d lam.val.transpose := by
    refine Submodule.sum_mem _ fun κ hκ => ?_
    have hne : κ ≠ lam := Finset.ne_of_mem_erase hκ
    rcases lexLT_trichotomy κ.val.transpose lam.val.transpose with hl | he | hg
    · rw [degreeEBasis_apply, pair_schur_e_vanish d κ (transposeShape d lam) hl, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · exact absurd (Subtype.ext (YoungDiagram.transpose_eq_iff.mp he)) hne
    · refine Submodule.smul_mem _ _ ?_
      have h1 := eAbove_mono d hg (ih κ hg)
      have h2 : degreeEBasis d (transposeShape d κ) ∈ EAbove d lam.val.transpose :=
        Submodule.subset_span ⟨transposeShape d κ, hg, rfl⟩
      have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (sgn κ.val) h2)
      rwa [sub_add_cancel] at this
  have hs : schur d lam - sgn lam.val • degreeEBasis d (transposeShape d lam) =
      -(sgn lam.val • rest) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_smul, sgn_sq, one_smul]
    abel
  rw [hs]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hrest)


open Classical in
/-- The two defining properties of `s'_λ` in Proposition 3.10. -/
def IsSPrime (d : ℕ) (lam : DegreeShape d) (x : degreePiece d) : Prop :=
  (∀ μ : DegreeShape d, LexLT lam.val.transpose μ.val →
      quotientPairing (x : Q) (ePartition μ.val) = 0) ∧
  ∃ b : DegreeShape d → ℤ, x = degreeEBasis d (transposeShape d lam) +
    ∑ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => LexLT lam.val.transpose μ.val),
      b μ • degreeEBasis d μ

open Classical in
theorem mem_eAbove_iff (d : ℕ) (κ : YoungDiagram) (y : degreePiece d) :
    y ∈ EAbove d κ ↔ ∃ b : DegreeShape d → ℤ,
      y = ∑ μ ∈ Finset.univ.filter (fun μ : DegreeShape d => LexLT κ μ.val),
        b μ • degreeEBasis d μ := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      refine ⟨fun ν => if ν = μ then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single μ]
      · simp
      · intro ν _ hν; simp [hν]
      · intro hn; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ⟩) hn
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b1, rfl⟩ := hx
      obtain ⟨b2, rfl⟩ := hy
      exact ⟨b1 + b2, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨a • b, by simp only [Finset.smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]⟩
  · rintro ⟨b, rfl⟩
    exact Submodule.sum_mem _ fun μ hμ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨μ, (Finset.mem_filter.mp hμ).2, rfl⟩)

theorem sub_mem_eAbove_of_isSPrime {d : ℕ} {lam : DegreeShape d} {x : degreePiece d}
    (hx : IsSPrime d lam x) :
    x - degreeEBasis d (transposeShape d lam) ∈ EAbove d lam.val.transpose := by
  obtain ⟨b, hb⟩ := hx.2
  rw [mem_eAbove_iff]
  exact ⟨b, by rw [hb, add_sub_cancel_left]⟩

theorem isSPrime_of_mem {d : ℕ} {lam : DegreeShape d} {x : degreePiece d}
    (h1 : ∀ μ : DegreeShape d, LexLT lam.val.transpose μ.val →
      quotientPairing (x : Q) (ePartition μ.val) = 0)
    (h2 : x - degreeEBasis d (transposeShape d lam) ∈ EAbove d lam.val.transpose) :
    IsSPrime d lam x := by
  refine ⟨h1, ?_⟩
  obtain ⟨b, hb⟩ := (mem_eAbove_iff d _ _).mp h2
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

/-- `s_κ ∈ span{e_μ : μ > λᵀ}` whenever `κᵀ > λᵀ`. -/
theorem schur_mem_eAbove (d : ℕ) (h311 : Identity311 d) {lam κ : DegreeShape d}
    (hk : LexLT lam.val.transpose κ.val.transpose) : schur d κ ∈ EAbove d lam.val.transpose := by
  have h1 := eAbove_mono d hk (schur_sub_e_mem d h311 κ)
  have h2 : degreeEBasis d (transposeShape d κ) ∈ EAbove d lam.val.transpose :=
    Submodule.subset_span ⟨transposeShape d κ, hk, rfl⟩
  have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (sgn κ.val) h2)
  rwa [sub_add_cancel] at this

/-- Existence: `sgn(λ) • s_λ` has both defining properties. -/
theorem isSPrime_sgn_schur (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d) :
    IsSPrime d lam (sgn lam.val • schur d lam) := by
  refine isSPrime_of_mem (fun μ hμ => ?_) ?_
  · rw [Submodule.coe_smul, map_zsmul, LinearMap.smul_apply, pair_schur_e_vanish d lam μ hμ,
      smul_zero]
  · have := Submodule.smul_mem _ (sgn lam.val) (schur_sub_e_mem d h311 lam)
    rwa [smul_sub, smul_smul, sgn_sq, one_smul] at this

/-- Uniqueness: any element with both defining properties equals `sgn(λ) • s_λ`. -/
theorem isSPrime_unique (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d)
    (x : degreePiece d) (hx : IsSPrime d lam x) : x = sgn lam.val • schur d lam := by
  have hs' := isSPrime_sgn_schur d h311 lam
  set y := x - sgn lam.val • schur d lam with hy
  have hyE : y ∈ EAbove d lam.val.transpose := by
    have := Submodule.sub_mem _ (sub_mem_eAbove_of_isSPrime hx) (sub_mem_eAbove_of_isSPrime hs')
    rwa [sub_sub_sub_cancel_right] at this
  have hyperp : ∀ μ : DegreeShape d, LexLT lam.val.transpose μ.val →
      quotientPairing (y : Q) (ePartition μ.val) = 0 := by
    intro μ hμ
    rw [hy, Submodule.coe_sub, map_sub, LinearMap.sub_apply, hx.1 μ hμ, hs'.1 μ hμ, sub_zero]
  have hall : ∀ κ : DegreeShape d, quotientPairing (schur d κ : Q) (y : Q) = 0 := by
    intro κ
    by_cases hk : LexLT lam.val.transpose κ.val.transpose
    · have hle : EAbove d lam.val.transpose ≤ LinearMap.ker (pairingMap d y) := by
        rw [EAbove, Submodule.span_le]
        rintro _ ⟨μ, hμ, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, pairingMap_apply, degreeEBasis_apply]
        rw [quotientPairing_symm]
        exact hyperp μ hμ
      have := hle (schur_mem_eAbove d h311 hk)
      simpa only [LinearMap.mem_ker, pairingMap_apply] using this
    · have hle : EAbove d lam.val.transpose ≤ LinearMap.ker (pairingMap d (schur d κ)) := by
        rw [EAbove, Submodule.span_le]
        rintro _ ⟨μ, hμ, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, pairingMap_apply, degreeEBasis_apply]
        rw [quotientPairing_symm]
        apply pair_schur_e_vanish
        rcases lexLT_trichotomy κ.val.transpose lam.val.transpose with h | h | h
        · exact lt_trans h hμ
        · rw [h]; exact hμ
        · exact absurd h hk
      have := hle hyE
      simp only [LinearMap.mem_ker, pairingMap_apply] at this
      rw [quotientPairing_symm]
      exact this
  have hexp := expansion d h311 y
  simp only [hall, mul_zero, zero_smul, Finset.sum_const_zero] at hexp
  exact sub_eq_zero.mp hexp

/-- **EK Proposition 3.10** (degree `d`, assuming exactly (3.11) in degree `d`). -/
theorem proposition_3_10 (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d) :
    (∃! x : degreePiece d, IsSPrime d lam x) ∧
    ∀ x : degreePiece d, IsSPrime d lam x →
      x = (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val) • schur d lam :=
  ⟨⟨_, isSPrime_sgn_schur d h311 lam, isSPrime_unique d h311 lam⟩, isSPrime_unique d h311 lam⟩


/-! ## The source normalisation `s'_(1ⁿ) = e_n` -/

/-- A one-row diagram `(d)` dominates every diagram of size `d`. -/
theorem dom_row {d : ℕ} (κ : YoungDiagram) (hκ : κ.rowLens = [d]) (μ : DegreeShape d)
    (hκd : κ.card = d) : Dom μ.val κ := by
  intro k
  cases k with
  | zero => rw [shapePrefix_zero, shapePrefix_zero]
  | succ k =>
    have hall : shapePrefix κ (k+1) = d := by
      rw [← hκd]
      unfold shapePrefix
      rw [Finset.filter_true_of_mem]
      · intro p hp
        rw [YoungDiagram.mem_cells] at hp
        have hlen : κ.colLen 0 = 1 := by
          rw [← YoungDiagram.length_rowLens, hκ]; rfl
        have : (p.1, 0) ∈ κ := κ.up_left_mem le_rfl (Nat.zero_le _) hp
        rw [YoungDiagram.mem_iff_lt_colLen, hlen] at this
        omega
    rw [hall]
    have hμ : μ.val.card = d := μ.property
    calc shapePrefix μ.val (k+1) ≤ μ.val.cells.card := Finset.card_filter_le _ _
      _ = d := hμ

/-- For `λ = (1ᵈ)` (i.e. `λᵀ = (d)`), the index set `{μ > λᵀ}` is empty. -/
theorem no_lex_above_row {d : ℕ} (lam : DegreeShape d) (hcol : lam.val.transpose.rowLens = [d])
    (μ : DegreeShape d) : ¬ LexLT lam.val.transpose μ.val := by
  intro h
  rcases lex_le_of_dom (dom_row (transposeShape d lam).val hcol μ (transposeShape d lam).property)
    with he | hl
  · rw [transposeShape_val] at he
    rw [← he] at h
    exact lt_irrefl _ h
  · exact lt_asymm h hl

/-- **Source normalisation** `s'_(1ᵈ) = e_d` is forced: under (3.11), for `λ = (1ᵈ)` the
unique `s'_λ` is `e_d`, i.e. `(-1)^{ℓ(w_λ)+C(λᵀ,2)} s_(1ᵈ) = e_d`. -/
theorem proposition_3_10_normalisation (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d)
    (hcol : lam.val.transpose.rowLens = [d]) :
    ((sgn lam.val • schur d lam : degreePiece d) : Q) = EKElementaryQuotient.e d := by
  have hx : IsSPrime d lam (degreeEBasis d (transposeShape d lam)) :=
    isSPrime_of_mem (fun μ hμ => absurd hμ (no_lex_above_row lam hcol μ))
      (by rw [sub_self]; exact Submodule.zero_mem _)
  rw [← isSPrime_unique d h311 lam _ hx, degreeEBasis_apply, transposeShape_val, ePartition, hcol]
  simp

/-! ## Sharpness: Proposition 3.10 (identification) is equivalent to (3.11) -/

/-- `(s_λ, w) = 0` for all `w ∈ span{e_μ : μ > λᵀ}` (unconditional). -/
theorem pair_schur_eAbove (d : ℕ) (lam : DegreeShape d) (w : degreePiece d)
    (hw : w ∈ EAbove d lam.val.transpose) : quotientPairing (schur d lam : Q) (w : Q) = 0 := by
  have hle : EAbove d lam.val.transpose ≤ LinearMap.ker (pairingMap d (schur d lam)) := by
    rw [EAbove, Submodule.span_le]
    rintro _ ⟨μ, hμ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, pairingMap_apply, degreeEBasis_apply]
    rw [quotientPairing_symm]
    exact pair_schur_e_vanish d lam μ hμ
  have := hle hw
  simp only [LinearMap.mem_ker, pairingMap_apply] at this
  rw [quotientPairing_symm]
  exact this

/-- Converse: if `sgn(λ) • s_λ` satisfies (1),(2) for every `λ ⊢ d`, then (3.11) holds. -/
theorem identity311_of_isSPrime (d : ℕ)
    (h : ∀ lam : DegreeShape d, IsSPrime d lam (sgn lam.val • schur d lam)) : Identity311 d := by
  -- s_κ ∈ span{e_μ : μ > λᵀ} whenever κᵀ > λᵀ
  have hmem : ∀ lam κ : DegreeShape d, LexLT lam.val.transpose κ.val.transpose →
      schur d κ ∈ EAbove d lam.val.transpose := by
    intro lam κ hk
    have h1 := eAbove_mono d hk (sub_mem_eAbove_of_isSPrime (h κ))
    have h2 : degreeEBasis d (transposeShape d κ) ∈ EAbove d lam.val.transpose :=
      Submodule.subset_span ⟨transposeShape d κ, hk, rfl⟩
    have h3 := Submodule.add_mem _ h1 h2
    rw [sub_add_cancel] at h3
    have h4 := Submodule.smul_mem _ (sgn κ.val) h3
    rwa [smul_smul, sgn_sq, one_smul] at h4
  intro lam μ
  split_ifs with hl
  · subst hl
    have hw := sub_mem_eAbove_of_isSPrime (h lam)
    have key : quotientPairing (schur d lam : Q) ((sgn lam.val • schur d lam : degreePiece d) : Q) =
        (-1 : ℤ) ^ EKSemiorthogonality.ell lam.val := by
      have hsplit : sgn lam.val • schur d lam = degreeEBasis d (transposeShape d lam) +
          (sgn lam.val • schur d lam - degreeEBasis d (transposeShape d lam)) := by abel
      rw [hsplit, Submodule.coe_add, map_add, pair_schur_eAbove d lam _ hw, add_zero,
        degreeEBasis_apply, transposeShape_val, pair_schur_e_diag]
    rw [Submodule.coe_smul, map_zsmul, smul_eq_mul] at key
    have h2 : quotientPairing (schur d lam : Q) (schur d lam : Q) =
        sgn lam.val * (-1 : ℤ) ^ EKSemiorthogonality.ell lam.val := by
      calc quotientPairing (schur d lam : Q) (schur d lam : Q)
          = sgn lam.val * (sgn lam.val * quotientPairing (schur d lam : Q) (schur d lam : Q)) := by
            rw [← mul_assoc, sgn_sq, one_mul]
        _ = sgn lam.val * (-1 : ℤ) ^ EKSemiorthogonality.ell lam.val := by rw [key]
    rw [h2, sgn, pow_add, mul_right_comm, sign_mul_self, one_mul]
  · rcases lexLT_trichotomy lam.val.transpose μ.val.transpose with hlt | he | hgt
    · exact pair_schur_eAbove d lam _ (hmem lam μ hlt)
    · exact absurd (Subtype.ext (YoungDiagram.transpose_eq_iff.mp he)) hl
    · rw [quotientPairing_symm]
      exact pair_schur_eAbove d μ _ (hmem μ lam hgt)

/-- The (3.11) hypothesis of `proposition_3_10` is sharp. -/
theorem proposition_3_10_iff_identity311 (d : ℕ) :
    (∀ lam : DegreeShape d, IsSPrime d lam (sgn lam.val • schur d lam)) ↔ Identity311 d :=
  ⟨identity311_of_isSPrime d, fun h311 lam => isSPrime_sgn_schur d h311 lam⟩

/-! ## By-product: E-half restricted nondegeneracy (source Lemma 2.15's use here) -/

/-- Under (3.11): an element of `span{e_μ : μ > λᵀ}` orthogonal to every such `e_μ` is 0. -/
theorem eAbove_restricted_nondeg (d : ℕ) (h311 : Identity311 d) (lam : DegreeShape d)
    (y : degreePiece d) (hy : y ∈ EAbove d lam.val.transpose)
    (hperp : ∀ μ : DegreeShape d, LexLT lam.val.transpose μ.val →
      quotientPairing (y : Q) (ePartition μ.val) = 0) : y = 0 := by
  have hs := isSPrime_sgn_schur d h311 lam
  have hx : IsSPrime d lam (y + sgn lam.val • schur d lam) := by
    refine isSPrime_of_mem (fun μ hμ => ?_) ?_
    · rw [Submodule.coe_add, map_add, LinearMap.add_apply, hperp μ hμ, hs.1 μ hμ, add_zero]
    · have := Submodule.add_mem _ hy (sub_mem_eAbove_of_isSPrime hs)
      rwa [← add_sub_assoc] at this
  have := isSPrime_unique d h311 lam _ hx
  rwa [add_eq_right] at this

/-! ## Unconditional for d ≤ 4: (3.11) discharged by exact computation

No general (3.9) ⇒ (3.11) implication is used or re-proved here (that is proved in
`EKSchurOrthonormal`, not in this module). Instead, for each d ≤ 4 an explicit hand family `S` in the
h-basis is checked to satisfy (3.6) with the literal odd Kostka numbers (kernel tables of
`EKProp310Controls`), so `S = s_λ` by uniqueness of the (3.6) solution, and its exact Gram
matrix is computed from the kernel M′ = (h,h) tables. Degrees 1–3 use the pre-registered
`hand1/2/3` of `EKProp310Controls`; degrees 0 and 4 are below. Hand derivation for d = 4
(inverse of the transposed Kostka table, rows (4),(3,1),(2,2),(2,1,1),(1⁴)):
`s_4 = h_4`, `s_31 = h_31 - h_4`, `s_22 = h_22 + h_31 - 2h_4`,
`s_211 = h_211 - h_22 - h_31 + h_4`, `s_1111 = h_1111 - h_211 + h_22 - h_4`;
Gram `diag(+1, -1, +1, -1, +1) = (-1)^{C(λᵀ,2)}` with `C(λᵀ,2) = 0,1,2,3,6`. -/

/-- (3.6) determines s uniquely, even when tested only in `Q`. -/
theorem schur_val_unique (d : ℕ) (S : DegreeShape d → Q)
    (hS : ∀ μ : DegreeShape d, hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • S lam)
    (lam : DegreeShape d) : (schur d lam : Q) = S lam := by
  have h1 : KostkaModuleInversion.transform d (fun l => (schur d l : Q)) =
      fun μ => hPartition μ.val := by
    funext μ
    have h := congrArg Subtype.val (schur_defining d μ)
    rw [degreeHBasis_apply] at h
    rw [h, Submodule.coe_sum]
    rfl
  have h2 : KostkaModuleInversion.transform d S = fun μ => hPartition μ.val := by
    funext μ
    exact (hS μ).symm
  exact congrFun ((KostkaModuleInversion.uniqueSolution d (fun μ => hPartition μ.val)).unique
    h1 h2) lam

/-- A hand family solving (3.6) with signed-orthonormal exact Gram matrix gives (3.11). -/
theorem identity311_of_hand (d : ℕ) (S : DegreeShape d → Q)
    (hS : ∀ μ : DegreeShape d, hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • S lam)
    (hG : ∀ lam μ : DegreeShape d, quotientPairing (S lam) (S μ) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0) : Identity311 d := by
  intro lam μ
  rw [schur_val_unique d S hS lam, schur_val_unique d S hS μ]
  exact hG lam μ

section HandFixtures
open EKProp310Controls

def hand0 : DegreeShape 0 → Q := fun _ => hPartition sh0.val

def hand4 : DegreeShape 4 → Q := fun lam =>
  if lam.val.rowLens = [4] then hPartition sh4.val
  else if lam.val.rowLens = [3,1] then hPartition sh31.val - hPartition sh4.val
  else if lam.val.rowLens = [2,2] then
    hPartition sh22.val + hPartition sh31.val - hPartition sh4.val - hPartition sh4.val
  else if lam.val.rowLens = [2,1,1] then
    hPartition sh211.val - hPartition sh22.val - hPartition sh31.val + hPartition sh4.val
  else hPartition sh1111.val - hPartition sh211.val + hPartition sh22.val - hPartition sh4.val

theorem hand0_defining (μ : DegreeShape 0) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • hand0 lam := by
  rw [sum0]
  rcases exhaust0 μ with rfl
  simp [hand0, K_0_0]

theorem hand4_defining (μ : DegreeShape 4) :
    hPartition μ.val = ∑ lam, signedKostka lam.val μ.val • hand4 lam := by
  rw [sum4]
  rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
  all_goals simp [hand4, K_4_4, K_4_31, K_4_22, K_4_211, K_4_1111, K_31_4, K_31_31, K_31_22,
    K_31_211, K_31_1111, K_22_4, K_22_31, K_22_22, K_22_211, K_22_1111, K_211_4, K_211_31,
    K_211_22, K_211_211, K_211_1111, K_1111_4, K_1111_31, K_1111_22, K_1111_211, K_1111_1111]
  all_goals abel

theorem hand0_gram (lam μ : DegreeShape 0) :
    quotientPairing (hand0 lam) (hand0 μ) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  rcases exhaust0 lam with rfl
  rcases exhaust0 μ with rfl
  simp [hand0, pair_hh, Mh_0_0, sh0_signs]

theorem hand4_gram (lam μ : DegreeShape 4) :
    quotientPairing (hand4 lam) (hand4 μ) =
      if lam = μ then (-1 : ℤ) ^ transposeChoose lam.val else 0 := by
  rcases exhaust4 lam with rfl|rfl|rfl|rfl|rfl
  all_goals rcases exhaust4 μ with rfl|rfl|rfl|rfl|rfl
  all_goals simp [hand4, pair_hh, Mh_4_4, Mh_4_31, Mh_4_22, Mh_4_211, Mh_4_1111, Mh_31_4,
    Mh_31_31, Mh_31_22, Mh_31_211, Mh_31_1111, Mh_22_4, Mh_22_31, Mh_22_22, Mh_22_211,
    Mh_22_1111, Mh_211_4, Mh_211_31, Mh_211_22, Mh_211_211, Mh_211_1111, Mh_1111_4,
    Mh_1111_31, Mh_1111_22, Mh_1111_211, Mh_1111_1111, sh4_signs, sh31_signs, sh22_signs,
    sh211_signs, sh1111_signs, shape_eq_iff]

/-- (3.11) in every degree d ≤ 4, by exact computation (no general (3.9) ⇒ (3.11)). -/
theorem identity311_le_four (d : ℕ) (hd : d ≤ 4) : Identity311 d := by
  interval_cases d
  · exact identity311_of_hand 0 hand0 hand0_defining hand0_gram
  · exact identity311_of_hand 1 hand1 hand1_defining hand1_gram
  · exact identity311_of_hand 2 hand2 hand2_defining hand2_gram
  · exact identity311_of_hand 3 hand3 hand3_defining hand3_gram
  · exact identity311_of_hand 4 hand4 hand4_defining hand4_gram

end HandFixtures

/-- **EK Proposition 3.10, unconditionally for |λ| ≤ 4.** -/
theorem proposition_3_10_le_four (d : ℕ) (hd : d ≤ 4) (lam : DegreeShape d) :
    (∃! x : degreePiece d, IsSPrime d lam x) ∧
    ∀ x : degreePiece d, IsSPrime d lam x →
      x = (-1 : ℤ) ^ (EKSemiorthogonality.ell lam.val + transposeChoose lam.val) • schur d lam :=
  proposition_3_10 d (identity311_le_four d hd) lam

end OddMath.Frontier.EKProp310
