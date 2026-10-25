/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Spanning

/-!
# Dot-minus-crossing filtration

Supporting the bounded cyclotomic separation step toward Brundan–Ellis,
*Super Kac–Moody 2-categories*, §8 Nondegeneracy Conjecture (research issue #345).
The integer score remembers dots lost by the crossing-only filtration.
This file establishes local score control and its compatibility with contexts;
it does not yet establish score-controlled PBW straightening or SKM independence.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA

/-- Number of dots minus number of crossings, without truncated subtraction. -/
def wordScore (gs : List PG) : ℤ := (gs.length : ℤ) - 2 * (crossCount gs : ℤ)

@[simp] theorem wordScore_nil : wordScore [] = 0 := rfl

@[simp] theorem wordScore_append (gs hs : List PG) :
    wordScore (gs ++ hs) = wordScore gs + wordScore hs := by
  simp only [wordScore, List.length_append, crossCount_append, Nat.cast_add]
  omega

@[simp] theorem wordScore_dot (p : ℕ) : wordScore [.dot p] = 1 := rfl
@[simp] theorem wordScore_cross (p : ℕ) : wordScore [.cross p] = -1 := rfl

/-- Effective score ignores out-of-range positioned generators, which `PG.ld`
interprets as empty layers. Counting those generators would make the filtration trivial. -/
def positionedScore (n : ℕ) (gs : List PG) : ℤ :=
  wordScore (gs.filter fun g => g.pos + g.width ≤ n)

@[simp] theorem positionedScore_append (n : ℕ) (gs hs : List PG) :
    positionedScore n (gs ++ hs) = positionedScore n gs + positionedScore n hs := by
  simp [positionedScore, List.filter_append]

 theorem positionedScore_eq_wordScore {n : ℕ} {gs : List PG}
    (h : ∀ g ∈ gs, g.pos + g.width ≤ n) : positionedScore n gs = wordScore gs := by
  unfold positionedScore
  congr 1
  exact List.filter_eq_self.mpr (by simpa using h)

@[simp] theorem wordScore_cw (σ : List ℕ) : wordScore (cw σ) = -(σ.length : ℤ) := by
  rw [wordScore, crossCount_cw]
  simp only [cw, List.length_reverse, List.length_map]
  omega

 theorem positionedScore_cw {n : ℕ} {σ : List ℕ}
    (h : Categorification.TypeA.ValidWord n σ) :
    positionedScore n (cw σ) = -(σ.length : ℤ) := by
  rw [positionedScore_eq_wordScore, wordScore_cw]
  intro g hg
  simp only [cw, List.mem_map, List.mem_reverse] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  have := h a ha
  simp only [PG.pos, PG.width]
  omega

 theorem positionedScore_nonneg_of_crossCount_zero (n : ℕ) (gs : List PG)
    (h : crossCount gs = 0) : 0 ≤ positionedScore n gs := by
  induction gs with
  | nil => simp [positionedScore]
  | cons g gs ih =>
    cases g with
    | dot p =>
      have hc : crossCount gs = 0 := by simpa [PG.isCross] using h
      have hi := ih hc
      simp only [positionedScore, List.filter_cons]
      split_ifs
      · simp only [wordScore, List.length_cons, crossCount_cons, PG.isCross,
          zero_add, Nat.cast_add, Nat.cast_one] at *
        unfold positionedScore wordScore at hi
        omega
      · exact hi
    | cross a => simp [PG.isCross] at h

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Span of positioned words whose dot-minus-crossing score is at least `s`. -/
def ScoreFilt (t t' : List I) (s : ℤ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ gs h, s ≤ positionedScore t.length gs ∧ cl D Sc t t' gs h = f}

theorem cl_mem_scoreFilt {t t' : List I} {gs : List PG}
    (h : SChain t (pl t gs) t') {s : ℤ} (hs : s ≤ positionedScore t.length gs) :
    cl D Sc t t' gs h ∈ ScoreFilt D Sc t t' s :=
  Submodule.subset_span ⟨gs, h, hs, rfl⟩

theorem scoreFilt_antitone {t t' : List I} {s r : ℤ} (h : s ≤ r) :
    ScoreFilt D Sc t t' r ≤ ScoreFilt D Sc t t' s :=
  Submodule.span_mono fun _ ⟨gs, hg, hs, e⟩ => ⟨gs, hg, h.trans hs, e⟩

/-- The existing local correction bounds retain enough information: zero crossings
implies nonnegative score, even though general crossing bounds forget the dots. -/
theorem filt_zero_le_scoreFilt_zero (t t' : List I) :
    Filt D Sc t t' 0 ≤ ScoreFilt D Sc t t' 0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨gs, hg, hc, rfl⟩
  apply cl_mem_scoreFilt D Sc hg
  exact positionedScore_nonneg_of_crossCount_zero _ _ (by omega)

/-- Lower scores add when a morphism is placed in a word context. -/
theorem comp_scoreFilt_comp {t t₁ t₂ t' : List I} (Q R : List PG)
    (h₁ : SChain t (pl t Q) t₁) (h₂ : SChain t₂ (pl t₂ R) t')
    {s : ℤ} {f : (pres D Sc).obj (ob D t₁) ⟶ (pres D Sc).obj (ob D t₂)}
    (hf : f ∈ ScoreFilt D Sc t₁ t₂ s) :
    cl D Sc t t₁ Q h₁ ≫ f ≫ cl D Sc t₂ t' R h₂ ∈
      ScoreFilt D Sc t t' (positionedScore t.length Q + s + positionedScore t₂.length R) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨gs, hg, hs, rfl⟩ := hx
    rw [cl_comp, cl_comp]
    have hlen₁ : t₁.length = t.length := length_of_sChain h₁
    have hlen₂ : t₂.length = t₁.length := length_of_sChain hg
    exact cl_mem_scoreFilt D Sc _ (by
      simp only [positionedScore_append]
      rw [hlen₁] at hs
      rw [hlen₂, hlen₁]
      omega)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.smul_mem _ c hx

/-- Local score control survives arbitrary positioned contexts. -/
theorem score_move_ctx {t t₁ t₂ t' : List I} (Q M M' R : List PG) (c : k)
    {s : ℤ} (hQ : SChain t (pl t Q) t₁) (hR : SChain t₂ (pl t₂ R) t')
    (hM : SChain t₁ (pl t₁ M) t₂) (hM' : SChain t₁ (pl t₁ M') t₂)
    (hmove : cl D Sc t₁ t₂ M hM - c • cl D Sc t₁ t₂ M' hM' ∈
      ScoreFilt D Sc t₁ t₂ s)
    (h : SChain t (pl t (Q ++ M ++ R)) t')
    (h' : SChain t (pl t (Q ++ M' ++ R)) t') :
    cl D Sc t t' (Q ++ M ++ R) h - c • cl D Sc t t' (Q ++ M' ++ R) h' ∈
      ScoreFilt D Sc t t' (positionedScore t.length Q + s + positionedScore t₂.length R) := by
  have e₁ : cl D Sc t t' (Q ++ M ++ R) h =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M hM ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  have e₂ : cl D Sc t t' (Q ++ M' ++ R) h' =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M' hM' ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [e₁, e₂]
  convert comp_scoreFilt_comp D Sc Q R hQ hR hmove using 1
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul]

theorem cross_cross_score {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h : SChain t₁ (pl t₁ [.cross a, .cross a]) t₂) :
    cl D Sc t₁ t₂ [.cross a, .cross a] h ∈ ScoreFilt D Sc t₁ t₂ 0 :=
  filt_zero_le_scoreFilt_zero D Sc _ _ (cross_cross_at D Sc ha h)

theorem slide_left_score {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.dot a, .cross a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.cross a, .dot (a + 1)]) t₂) :
    ∃ c : k, c * c = 1 ∧ cl D Sc t₁ t₂ [.dot a, .cross a] h₁ -
      c • cl D Sc t₁ t₂ [.cross a, .dot (a + 1)] h₂ ∈ ScoreFilt D Sc t₁ t₂ 0 := by
  obtain ⟨c, hc, hm⟩ := slide_left_at D Sc ha h₁ h₂
  exact ⟨c, hc, filt_zero_le_scoreFilt_zero D Sc _ _ hm⟩

theorem slide_right_score {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.cross a, .dot a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.dot (a + 1), .cross a]) t₂) :
    ∃ c : k, c * c = 1 ∧ cl D Sc t₁ t₂ [.cross a, .dot a] h₁ -
      c • cl D Sc t₁ t₂ [.dot (a + 1), .cross a] h₂ ∈ ScoreFilt D Sc t₁ t₂ 0 := by
  obtain ⟨c, hc, hm⟩ := slide_right_at D Sc ha h₁ h₂
  exact ⟨c, hc, filt_zero_le_scoreFilt_zero D Sc _ _ hm⟩

theorem braid_score {t₁ t₂ : List I} {a : ℕ} (ha : a + 2 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.cross a, .cross (a + 1), .cross a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.cross (a + 1), .cross a, .cross (a + 1)]) t₂) :
    cl D Sc t₁ t₂ [.cross a, .cross (a + 1), .cross a] h₁ -
      cl D Sc t₁ t₂ [.cross (a + 1), .cross a, .cross (a + 1)] h₂ ∈
        ScoreFilt D Sc t₁ t₂ 0 :=
  filt_zero_le_scoreFilt_zero D Sc _ _ (braid_at D Sc ha h₁ h₂)

/-- Joint span, retaining crossing count and score on the same representatives.
An intersection of the two separate spans would not justify joint induction. -/
def BoundedScore (t t' : List I) (m : ℕ) (s : ℤ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ gs h, crossCount gs ≤ m ∧
    s ≤ positionedScore t.length gs ∧ cl D Sc t t' gs h = f}

theorem cl_mem_boundedScore {t t' : List I} {gs : List PG}
    (h : SChain t (pl t gs) t') {m : ℕ} {s : ℤ}
    (hm : crossCount gs ≤ m) (hs : s ≤ positionedScore t.length gs) :
    cl D Sc t t' gs h ∈ BoundedScore D Sc t t' m s :=
  Submodule.subset_span ⟨gs, h, hm, hs, rfl⟩

theorem boundedScore_mono {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m ≤ n) (hs : s ≤ r) :
    BoundedScore D Sc t t' m r ≤ BoundedScore D Sc t t' n s :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, hd, e⟩ =>
    ⟨gs, hg, hc.trans hm, hs.trans hd, e⟩

theorem boundedScore_le_filt (t t' : List I) (m : ℕ) (s : ℤ) :
    BoundedScore D Sc t t' m s ≤ Filt D Sc t t' m :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, _, e⟩ => ⟨gs, hg, hc, e⟩

theorem boundedScore_le_scoreFilt (t t' : List I) (m : ℕ) (s : ℤ) :
    BoundedScore D Sc t t' m s ≤ ScoreFilt D Sc t t' s :=
  Submodule.span_mono fun _ ⟨gs, hg, _, hs, e⟩ => ⟨gs, hg, hs, e⟩

theorem filt_zero_le_boundedScore_zero (t t' : List I) :
    Filt D Sc t t' 0 ≤ BoundedScore D Sc t t' 0 0 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨gs, hg, hc, rfl⟩
  exact cl_mem_boundedScore D Sc hg hc
    (positionedScore_nonneg_of_crossCount_zero _ _ (by omega))

theorem comp_boundedScore_comp {t t₁ t₂ t' : List I} (Q R : List PG)
    (h₁ : SChain t (pl t Q) t₁) (h₂ : SChain t₂ (pl t₂ R) t')
    {m : ℕ} {s : ℤ} {f : (pres D Sc).obj (ob D t₁) ⟶ (pres D Sc).obj (ob D t₂)}
    (hf : f ∈ BoundedScore D Sc t₁ t₂ m s) :
    cl D Sc t t₁ Q h₁ ≫ f ≫ cl D Sc t₂ t' R h₂ ∈
      BoundedScore D Sc t t' (crossCount Q + m + crossCount R)
        (positionedScore t.length Q + s + positionedScore t₂.length R) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨gs, hg, hc, hs, rfl⟩ := hx
    rw [cl_comp, cl_comp]
    have hlen₁ : t₁.length = t.length := length_of_sChain h₁
    have hlen₂ : t₂.length = t₁.length := length_of_sChain hg
    apply cl_mem_boundedScore D Sc _
    · simp only [crossCount_append]; omega
    · simp only [positionedScore_append]
      rw [hlen₁] at hs
      rw [hlen₂, hlen₁]
      omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.smul_mem _ c hx

/-- A local correction with no crossings can be used in the simultaneous
crossing/score induction, with the exact scores of both surrounding words. -/
theorem bounded_correction_ctx {t t₁ t₂ t' : List I} (Q M M' R : List PG) (c : k)
    (hQ : SChain t (pl t Q) t₁) (hR : SChain t₂ (pl t₂ R) t')
    (hM : SChain t₁ (pl t₁ M) t₂) (hM' : SChain t₁ (pl t₁ M') t₂)
    (hmove : cl D Sc t₁ t₂ M hM - c • cl D Sc t₁ t₂ M' hM' ∈ Filt D Sc t₁ t₂ 0)
    (h : SChain t (pl t (Q ++ M ++ R)) t')
    (h' : SChain t (pl t (Q ++ M' ++ R)) t') :
    cl D Sc t t' (Q ++ M ++ R) h - c • cl D Sc t t' (Q ++ M' ++ R) h' ∈
      BoundedScore D Sc t t' (crossCount Q + crossCount R)
        (positionedScore t.length Q + positionedScore t₂.length R) := by
  have e₁ : cl D Sc t t' (Q ++ M ++ R) h =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M hM ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  have e₂ : cl D Sc t t' (Q ++ M' ++ R) h' =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M' hM' ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [e₁, e₂]
  have hb := comp_boundedScore_comp D Sc Q R hQ hR
    (filt_zero_le_boundedScore_zero D Sc _ _ hmove)
  simpa only [add_zero, Preadditive.sub_comp, Preadditive.comp_sub,
    Linear.smul_comp, Linear.comp_smul] using hb

/-- Strict crossing bound used in the simultaneous straightening induction. -/
def ScoreLow (t t' : List I) (n : ℕ) (s : ℤ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ gs h, crossCount gs < n ∧
    s ≤ positionedScore t.length gs ∧ cl D Sc t t' gs h = f}

theorem boundedScore_le_scoreLow {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m < n) (hs : s ≤ r) :
    BoundedScore D Sc t t' m r ≤ ScoreLow D Sc t t' n s :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, hd, e⟩ =>
    ⟨gs, hg, lt_of_le_of_lt hc hm, hs.trans hd, e⟩

theorem scoreLow_mono {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m ≤ n) (hs : s ≤ r) :
    ScoreLow D Sc t t' m r ≤ ScoreLow D Sc t t' n s :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, hd, e⟩ =>
    ⟨gs, hg, lt_of_lt_of_le hc hm, hs.trans hd, e⟩

/-- A unit leading coefficient with a jointly controlled correction. -/
def WeightedApprox {t t' : List I} (n : ℕ) (s : ℤ)
    (x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) : Prop :=
  ∃ c : k, IsUnit c ∧ x - c • y ∈ ScoreLow D Sc t t' n s

theorem WeightedApprox.refl {t t' : List I} (n : ℕ) (s : ℤ)
    (x : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    WeightedApprox D Sc n s x x := by
  exact ⟨1, isUnit_one, by simp⟩

theorem WeightedApprox.symm {t t' : List I} {n : ℕ} {s : ℤ}
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h : WeightedApprox D Sc n s x y) : WeightedApprox D Sc n s y x := by
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨u, rfl⟩ := hc
  refine ⟨↑u⁻¹, Units.isUnit _, ?_⟩
  have hm := Submodule.smul_mem _ (-(↑u⁻¹ : k)) h
  convert hm using 1
  rw [smul_sub, smul_smul]
  simp [sub_eq_add_neg, add_comm]

theorem WeightedApprox.trans {t t' : List I} {n : ℕ} {s : ℤ}
    {x y z : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h₁ : WeightedApprox D Sc n s x y) (h₂ : WeightedApprox D Sc n s y z) :
    WeightedApprox D Sc n s x z := by
  obtain ⟨c, hc, h₁⟩ := h₁
  obtain ⟨d, hd, h₂⟩ := h₂
  refine ⟨c * d, hc.mul hd, ?_⟩
  have hm := Submodule.add_mem _ h₁ (Submodule.smul_mem _ c h₂)
  convert hm using 1
  rw [smul_sub, smul_smul]
  abel

theorem WeightedApprox.mono {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m ≤ n) (hs : s ≤ r)
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h : WeightedApprox D Sc m r x y) : WeightedApprox D Sc n s x y := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, scoreLow_mono D Sc hm hs h⟩

theorem weightedApprox_of_bounded {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m < n) (hs : s ≤ r) (c : k) (hc : IsUnit c)
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h : x - c • y ∈ BoundedScore D Sc t t' m r) : WeightedApprox D Sc n s x y :=
  ⟨c, hc, boundedScore_le_scoreLow D Sc hm hs h⟩

theorem weighted_approx_step {t t' : List I} (P : List PG) {n : ℕ} {σ σ' : List ℕ}
    (hs : BraidStep σ σ') (hv : ValidWord n σ) (hn : t.length = n)
    (h : SChain t (pl t (P ++ cw σ)) t') (h' : SChain t (pl t (P ++ cw σ')) t') :
    WeightedApprox D Sc (crossCount P + σ.length)
      (positionedScore t.length P - (σ.length : ℤ)) (cl D Sc t t' (P ++ cw σ) h)
      (cl D Sc t t' (P ++ cw σ') h') := by
  cases hs with
  | comm α β hab =>
    rename_i a b
    have hb : b + 1 < n := hv b (by simp)
    set Q := P ++ cw β
    have e₁ : P ++ cw (α ++ [a, b] ++ β) = Q ++ [PG.cross b, PG.cross a] ++ cw α := by
      simp [Q, cw]
    have e₂ : P ++ cw (α ++ [b, a] ++ β) = Q ++ [PG.cross a, PG.cross b] ++ cw α := by
      simp [Q, cw]
    rw [cl_eq_of_eq e₁, cl_eq_of_eq e₂]
    set t₁ := tgt t Q
    have hl : t₁.length = n := by simp [t₁, hn]
    have hM : SChain t₁ (pl t₁ [PG.cross b, PG.cross a]) (tgt t₁ [PG.cross b, PG.cross a]) :=
      sChain_pl _ _
    have hM' : SChain t₁ (pl t₁ [PG.cross a, PG.cross b]) (tgt t₁ [PG.cross b, PG.cross a]) :=
      sChain_of_tgt (sChain_pl _ _) (by
        have := tgt_cw_eq (σ := [b, a]) (σ' := [a, b]) (n := n)
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega)
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega)
          (by simp [sadj_comm n (Or.inr hab)]) hl
        simpa [cw] using this.symm)
    have hR : SChain (tgt t₁ [PG.cross b, PG.cross a])
        (pl (tgt t₁ [PG.cross b, PG.cross a]) (cw α)) t' := by
      have key : tgt t (Q ++ [PG.cross b, PG.cross a] ++ cw α) = t' := by
        rw [← e₁]; exact tgt_eq h
      have : tgt (tgt t₁ [PG.cross b, PG.cross a]) (cw α) = t' := by
        rw [← key]; simp only [t₁, tgt_append]
      exact this ▸ sChain_pl _ _
    obtain ⟨c, hc, hsw⟩ := far_swap D Sc (t₁ := t₁) (PG.cross a) (PG.cross b)
      (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) hM' hM
    have hmove : cl D Sc t₁ _ [PG.cross b, PG.cross a] hM -
        c • cl D Sc t₁ _ [PG.cross a, PG.cross b] hM' ∈ Filt D Sc t₁ _ 0 := by
      rw [hsw, smul_smul, hc, one_smul, sub_self]; exact Submodule.zero_mem _
    refine weightedApprox_of_bounded D Sc ?_ ?_ c (Units.mk c c hc hc).isUnit
      (bounded_correction_ctx D Sc Q _ _ (cw α) c (sChain_pl t Q) hR hM hM' hmove _ _)
    · simp [Q]; omega
    · have hvα : ValidWord n α := fun x hx => hv x (by simp only [List.mem_append]; aesop)
      have hvβ : ValidWord n β := fun x hx => hv x (by simp only [List.mem_append]; aesop)
      simp only [Q, positionedScore_append, length_tgt, t₁, hn,
        positionedScore_cw hvα, positionedScore_cw hvβ,
        List.length_append, List.length_cons, List.length_nil, Nat.cast_add]
      omega
  | braid α β a =>
    have ha : a + 1 + 1 < n := hv (a + 1) (by simp)
    set Q := P ++ cw β
    have e₁ : P ++ cw (α ++ [a, a + 1, a] ++ β) =
        Q ++ [PG.cross a, PG.cross (a + 1), PG.cross a] ++ cw α := by
      simp [Q, cw]
    have e₂ : P ++ cw (α ++ [a + 1, a, a + 1] ++ β) =
        Q ++ [PG.cross (a + 1), PG.cross a, PG.cross (a + 1)] ++ cw α := by
      simp [Q, cw]
    rw [cl_eq_of_eq e₁, cl_eq_of_eq e₂]
    set t₁ := tgt t Q
    have hl : t₁.length = n := by simp [t₁, hn]
    set M := [PG.cross a, PG.cross (a + 1), PG.cross a]
    set M' := [PG.cross (a + 1), PG.cross a, PG.cross (a + 1)]
    have hM : SChain t₁ (pl t₁ M) (tgt t₁ M) := sChain_pl _ _
    have hM' : SChain t₁ (pl t₁ M') (tgt t₁ M) :=
      sChain_of_tgt (sChain_pl _ _) (by
        have := tgt_cw_eq (σ := [a + 1, a, a + 1]) (σ' := [a, a + 1, a]) (n := n)
          (by intro x hx; simp at hx; omega) (by intro x hx; simp at hx; omega)
          (by simp only [wordProd_cons, wordProd_nil, mul_one, ← mul_assoc]
              exact (sadj_braid (by omega)).symm) hl
        simpa [cw, M, M'] using this.symm)
    have hR : SChain (tgt t₁ M) (pl (tgt t₁ M) (cw α)) t' := by
      have key : tgt t (Q ++ M ++ cw α) = t' := by
        rw [← e₁]; exact tgt_eq h
      have : tgt (tgt t₁ M) (cw α) = t' := by
        rw [← key]; simp only [t₁, tgt_append]
      exact this ▸ sChain_pl _ _
    have hmove := braid_at D Sc (t₁ := t₁) (a := a) (by omega) hM hM'
    rw [← one_smul k (cl D Sc t₁ _ M' hM')] at hmove
    refine weightedApprox_of_bounded D Sc ?_ ?_ 1 isUnit_one
      (bounded_correction_ctx D Sc Q M M' (cw α) 1 (sChain_pl t Q) hR hM hM' hmove _ _)
    · simp [Q]; omega
    · have hvα : ValidWord n α := fun x hx => hv x (by simp only [List.mem_append]; aesop)
      have hvβ : ValidWord n β := fun x hx => hv x (by simp only [List.mem_append]; aesop)
      simp only [Q, positionedScore_append, length_tgt, t₁, hn,
        positionedScore_cw hvα, positionedScore_cw hvβ,
        List.length_append, List.length_cons, List.length_nil, Nat.cast_add]
      omega


theorem weighted_braid_move {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n) {σ σ' : List ℕ}
    (hb : BraidEquiv σ σ') (hv : ValidWord n σ)
    (h : SChain t (pl t (P ++ cw σ)) t') (h' : SChain t (pl t (P ++ cw σ')) t') :
    WeightedApprox D Sc (crossCount P + σ.length)
      (positionedScore t.length P - (σ.length : ℤ)) (cl D Sc t t' (P ++ cw σ) h)
      (cl D Sc t t' (P ++ cw σ') h') := by
  induction hb with
  | rel σ σ' hs => exact weighted_approx_step D Sc P hs hv hn h h'
  | refl => exact WeightedApprox.refl D Sc _ _ _
  | symm σ σ' hb ih =>
    have hv' : ValidWord n σ := (BraidEquiv.validWord_iff hb).mpr hv
    have := WeightedApprox.symm D Sc (ih hv' h' h)
    rwa [BraidEquiv.length_eq hb] at this
  | trans σ σ'' σ' hb₁ hb₂ ih₁ ih₂ =>
    have hv'' : ValidWord n σ'' := (BraidEquiv.validWord_iff hb₁).mp hv
    have h'' := sChain_of_braid P hb₁ hv hn h
    have := ih₂ hv'' h'' h'
    rw [← BraidEquiv.length_eq hb₁] at this
    exact WeightedApprox.trans D Sc (ih₁ hv h h'') this


end OddMath.QuiverHecke
