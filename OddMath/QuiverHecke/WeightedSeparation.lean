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
This file establishes score-controlled affine PBW straightening through the
actual positioned relations. It does not assert SKM independence.
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

 theorem positionedScore_cross {n a : ℕ} (h : a + 1 < n) :
    positionedScore n [.cross a] = -1 := by
  rw [positionedScore_eq_wordScore, wordScore_cross]
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  simp only [PG.pos, PG.width]
  omega

 theorem positionedScore_dot {n p : ℕ} (h : p < n) :
    positionedScore n [.dot p] = 1 := by
  rw [positionedScore_eq_wordScore, wordScore_dot]
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  simp only [PG.pos, PG.width]
  omega

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


theorem weighted_approx_ctx {t t' : List I} (Q M M' R : List PG) (c : k) (hc : IsUnit c)
    (h : SChain t (pl t (Q ++ M ++ R)) t')
    (hM : SChain (tgt t Q) (pl (tgt t Q) M) (tgt (tgt t Q) M))
    (hM' : SChain (tgt t Q) (pl (tgt t Q) M') (tgt (tgt t Q) M))
    (hmove : cl D Sc _ _ M hM - c • cl D Sc _ _ M' hM' ∈ Filt D Sc _ _ 0) {N : ℕ}
    (hN : crossCount Q + crossCount R < N) {s : ℤ}
    (hs : s ≤ positionedScore t.length Q + positionedScore t.length R) :
    ∃ h' : SChain t (pl t (Q ++ M' ++ R)) t',
      WeightedApprox D Sc N s (cl D Sc t t' (Q ++ M ++ R) h) (cl D Sc t t' (Q ++ M' ++ R) h') := by
  have hR : SChain (tgt (tgt t Q) M) (pl (tgt (tgt t Q) M) R) t' := by
    have : tgt (tgt (tgt t Q) M) R = t' := by rw [← tgt_append, ← tgt_append]; exact tgt_eq (by simpa only [List.append_assoc] using h)
    exact this ▸ sChain_pl _ _
  have h' : SChain t (pl t (Q ++ M' ++ R)) t' :=
    sChain_append_of (sChain_append_of (sChain_pl t Q) hM') hR
  exact ⟨h', weightedApprox_of_bounded D Sc hN (by simpa using hs) c hc
    (bounded_correction_ctx D Sc Q M M' R c (sChain_pl t Q) hR hM hM' hmove h h')⟩


theorem weighted_dot_down {t t' : List I} (P : List PG) {n : ℕ} (hn : t.length = n) (σ : List ℕ)
    (hv : ValidWord n σ) (p : ℕ) (hp : p < n) (R : List PG)
    (h : SChain t (pl t (P ++ cw σ ++ [PG.dot p] ++ R)) t') :
    ∃ h' : SChain t (pl t (P ++ [PG.dot ((wordProd n σ)⁻¹ ⟨p, hp⟩)] ++ cw σ ++ R)) t',
      WeightedApprox D Sc (crossCount P + σ.length + crossCount R)
        (positionedScore t.length P - (σ.length : ℤ) + 1 + positionedScore t.length R) (cl D Sc t t' _ h)
        (cl D Sc t t' _ h') := by
  induction σ generalizing p R with
  | nil =>
    have e : P ++ cw [] ++ [PG.dot p] ++ R =
        P ++ [PG.dot ((wordProd n [])⁻¹ ⟨p, hp⟩)] ++ cw [] ++ R := by simp
    exact ⟨e ▸ h, by rw [cl_eq_cl e h (e ▸ h)]; exact WeightedApprox.refl D Sc _ _ _⟩
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    set Q := P ++ cw σ
    have e₁ : P ++ cw (a :: σ) ++ [PG.dot p] ++ R = Q ++ [PG.cross a, PG.dot p] ++ R := by
      simp [Q, cw_cons]
    have hl : (tgt t Q).length = n := by simp [hn]
    have hM : SChain (tgt t Q) (pl (tgt t Q) [PG.cross a, PG.dot p])
        (tgt (tgt t Q) [PG.cross a, PG.dot p]) := sChain_pl _ _
    obtain ⟨c, hc, h₂, hm⟩ :=
      cross_dot_move (D := D) (Sc := Sc) (by omega) (by omega) hM
    obtain ⟨h₃, hA⟩ := weighted_approx_ctx D Sc Q _ _ R c hc (e₁ ▸ h) hM h₂ hm
      (N := crossCount P + (a :: σ).length + crossCount R) (by simp [Q])
      (s := positionedScore t.length P - ((a :: σ).length : ℤ) + 1 + positionedScore t.length R)
      (by
        have hvσ : ValidWord n σ := fun x hx => hv x (by simp [hx])
        simp only [Q, positionedScore_append, hn, positionedScore_cw hvσ,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        omega)
    have hp' : swapNat a p < n := by unfold swapNat; split_ifs <;> omega
    have e₂ : Q ++ [PG.dot (swapNat a p), PG.cross a] ++ R =
        P ++ cw σ ++ [PG.dot (swapNat a p)] ++ ([PG.cross a] ++ R) := by
      simp [Q]
    obtain ⟨h₄, hB⟩ :=
      ih (fun x hx => hv x (by simp [hx])) (swapNat a p) hp' ([PG.cross a] ++ R) (e₂ ▸ h₃)
    have hq : (((wordProd n σ)⁻¹ ⟨swapNat a p, hp'⟩ : Fin n) : ℕ) =
        (((wordProd n (a :: σ))⁻¹ ⟨p, hp⟩ : Fin n) : ℕ) := by
      rw [wordProd_cons, mul_inv_rev, sadj_inv, Equiv.Perm.mul_apply]
      congr 2
      ext; rw [sadj_val_of_lt ha]
    have e₃ : P ++ [PG.dot ((wordProd n σ)⁻¹ ⟨swapNat a p, hp'⟩)] ++ cw σ ++ ([PG.cross a] ++ R) =
        P ++ [PG.dot ((wordProd n (a :: σ))⁻¹ ⟨p, hp⟩)] ++ cw (a :: σ) ++ R := by
      rw [← hq]; simp [cw_cons]
    refine ⟨e₃ ▸ h₄, ?_⟩
    rw [cl_eq_cl e₁ h (e₁ ▸ h), ← cl_eq_cl e₃ h₄ (e₃ ▸ h₄)]
    rw [cl_eq_cl e₂ h₃ (e₂ ▸ h₃)] at hA
    apply WeightedApprox.trans D Sc hA
    apply WeightedApprox.mono D Sc (by simp [PG.isCross]; omega) _ hB
    simp only [positionedScore_append, hn, positionedScore_cross ha,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    omega


theorem cl_mem_boundedScore_of_hasRepeat {t t' : List I} (P R : List PG) {n : ℕ} (hn : t.length = n)
    {σ : List ℕ} (hv : ValidWord n σ) (hr : HasRepeat σ)
    (h : SChain t (pl t (P ++ cw σ ++ R)) t') :
    cl D Sc t t' _ h ∈ BoundedScore D Sc t t' (crossCount P + (σ.length - 2) + crossCount R)
      (positionedScore t.length P - (σ.length : ℤ) + positionedScore t.length R) := by
  obtain ⟨α, β, b, rfl⟩ := hr
  have hb : b + 1 < n := hv b (by simp)
  have e : P ++ cw (α ++ [b, b] ++ β) ++ R =
      (P ++ cw β) ++ [PG.cross b, PG.cross b] ++ (cw α ++ R) := by simp [cw]
  rw [cl_eq_cl e h (e ▸ h)]
  set Q := P ++ cw β
  have hM : SChain (tgt t Q) (pl (tgt t Q) [PG.cross b, PG.cross b])
      (tgt (tgt t Q) [PG.cross b, PG.cross b]) := sChain_pl _ _
  have hR := sChain_suffix (e ▸ h)
  have key : cl D Sc t t' (Q ++ [PG.cross b, PG.cross b] ++ (cw α ++ R)) (e ▸ h) =
      cl D Sc t _ Q (sChain_pl t Q) ≫ cl D Sc _ _ _ hM ≫ cl D Sc _ t' _ hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [key]
  refine boundedScore_mono D Sc ?_ ?_ (comp_boundedScore_comp D Sc Q _ _ hR
    (filt_zero_le_boundedScore_zero D Sc _ _
      (cross_cross_at D Sc (by simp [hn]; omega) hM)))
  · simp [Q]; omega
  · have hvα : ValidWord n α := fun x hx => hv x (by simp only [List.mem_append]; aesop)
    have hvβ : ValidWord n β := fun x hx => hv x (by simp only [List.mem_append]; aesop)
    simp only [Q, positionedScore_append, length_tgt, hn,
      positionedScore_cw hvα, positionedScore_cw hvβ,
      List.length_append, List.length_cons, List.length_nil, Nat.cast_add]
    omega


theorem WeightedApprox.mem {t t' : List I} {N : ℕ} {s : ℤ}
    {x y : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (h : WeightedApprox D Sc N s x y)
    {M : Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))}
    (hM : ScoreLow D Sc t t' N s ≤ M) (hy : y ∈ M) : x ∈ M := by
  obtain ⟨c, -, h⟩ := h
  have hm := M.add_mem (hM h) (M.smul_mem c hy)
  simpa using hm

/-- Canonical affine normal forms with simultaneous crossing and score bounds. -/
def WeightedNF (t t' : List I) (m : ℕ) (s : ℤ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
    ∃ w : Equiv.Perm (Fin t.length), length t.length w ≤ m ∧
      s ≤ (l.length : ℤ) - (length t.length w : ℤ) ∧
      ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f}

theorem weightedNF_mono {t t' : List I} {m n : ℕ} {s r : ℤ}
    (hm : m ≤ n) (hs : s ≤ r) : WeightedNF D Sc t t' m r ≤ WeightedNF D Sc t t' n s :=
  Submodule.span_mono fun _ ⟨l, hl, hf, w, hw, hd, h, e⟩ =>
    ⟨l, hl, hf, w, hw.trans hm, hs.trans hd, h, e⟩

 theorem positionedScore_dots {n : ℕ} {l : List ℕ} (hl : ∀ p ∈ l, p < n) :
    positionedScore n (l.map PG.dot) = l.length := by
  rw [positionedScore_eq_wordScore]
  · simp [wordScore]
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    have := hl p hp
    simp only [PG.pos, PG.width]
    omega

theorem weighted_nf_comp_dot {t t₀ t' : List I} {m : ℕ} {s : ℤ} (hlow : ScoreLow D Sc t t' m (s + 1) ≤ WeightedNF D Sc t t' m (s + 1))
    {p : ℕ} (hp : p < t₀.length) (hg : SChain t₀ (pl t₀ [PG.dot p]) t')
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀)} (hf : f ∈ WeightedNF D Sc t t₀ m s) :
    f ≫ cl D Sc t₀ t' [PG.dot p] hg ∈ WeightedNF D Sc t t' m (s + 1) := by
  obtain rfl : t₀ = t' := tgt_eq hg
  refine span_comp_mem _ (fun s hs => ?_) hf
  obtain ⟨l, hs, hl, w, hw, hd, h, rfl⟩ := hs
  rw [cl_comp]
  set σ := canWord t.length w
  have hp' : p < t.length := by rw [← length_of_sChain h]; exact hp
  have e : l.map PG.dot ++ cw σ ++ [PG.dot p] = l.map PG.dot ++ cw σ ++ [PG.dot p] ++ [] := by
    simp
  rw [cl_eq_cl e _ (e ▸ sChain_append_of h hg)]
  obtain ⟨h', hA⟩ := weighted_dot_down D Sc (l.map PG.dot) rfl σ
    (validWord_canWord t.length w) p hp' [] (e ▸ sChain_append_of h hg)
  set q : ℕ := (((wordProd t.length σ)⁻¹ ⟨p, hp'⟩ : Fin t.length) : ℕ)
  have hq : q < t.length := Fin.is_lt _
  have e' : l.map PG.dot ++ [PG.dot q] ++ cw σ ++ [] = [] ++ (l ++ [q]).map PG.dot ++ cw σ := by
    simp
  have hl' : ∀ x ∈ l ++ [q], x < t.length := by
    intro x hx; simp at hx; rcases hx with hx | rfl; exacts [hl x hx, hq]
  obtain ⟨c, hc, h'', he⟩ := dots_perm (D := D) (Sc := Sc) [] (cw σ)
    ((List.perm_append_singleton q l).trans (List.perm_orderedInsert (· ≤ ·) q l).symm) hl'
    (e' ▸ h')
  rw [cl_eq_cl e' h' (e' ▸ h'), he] at hA
  have hscore : s + 1 ≤ positionedScore t.length (l.map PG.dot) - (σ.length : ℤ) + 1 +
      positionedScore t.length [] := by
    rw [positionedScore_dots hl]
    simp only [positionedScore, List.filter_nil, wordScore_nil,
      add_zero, σ, length_canWord]
    omega
  refine WeightedApprox.mem D Sc hA ((scoreLow_mono D Sc
      (by simp [σ, length_canWord]; omega) hscore).trans hlow)
    (Submodule.smul_mem _ c (Submodule.subset_span ?_))
  refine ⟨_, hs.orderedInsert q l, ?_, w, hw, ?_, by simpa using h'', rfl⟩
  · intro x hx
    rcases (List.mem_orderedInsert (· ≤ ·)).mp hx with rfl | hx
    exacts [hq, hl x hx]
  · have he := (List.perm_orderedInsert (· ≤ ·) q l).length_eq
    simp only [List.length_cons] at he
    omega


theorem weighted_nf_comp_cross {t t₀ t' : List I} {m : ℕ} {s : ℤ}
    (hlow : ScoreLow D Sc t t' (m + 1) (s - 1) ≤ WeightedNF D Sc t t' (m + 1) (s - 1))
    {a : ℕ} (ha : a + 1 < t₀.length) (hg : SChain t₀ (pl t₀ [PG.cross a]) t')
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t₀)} (hf : f ∈ WeightedNF D Sc t t₀ m s) :
    f ≫ cl D Sc t₀ t' [PG.cross a] hg ∈ WeightedNF D Sc t t' (m + 1) (s - 1) := by
  refine span_comp_mem _ (fun s hs => ?_) hf
  obtain ⟨l, hs, hl, w, hw, hd, h, rfl⟩ := hs
  rw [cl_comp]
  set σ := canWord t.length w
  have ha' : a + 1 < t.length := by rw [← length_of_sChain h]; exact ha
  have hv : ValidWord t.length (a :: σ) := by
    intro x hx; simp at hx; rcases hx with rfl | hx
    exacts [ha', validWord_canWord t.length w x hx]
  have hσ : σ.length = length t.length w := length_canWord t.length w
  have e : l.map PG.dot ++ cw σ ++ [PG.cross a] = l.map PG.dot ++ cw (a :: σ) := by
    simp [cw_cons]
  rw [cl_eq_cl e _ (e ▸ sChain_append_of h hg)]
  set h₀ := e ▸ sChain_append_of h hg
  have hlow' : ScoreLow D Sc t t' (crossCount (l.map PG.dot) + (a :: σ).length)
      (positionedScore t.length (l.map PG.dot) - ((a :: σ).length : ℤ)) ≤
      WeightedNF D Sc t t' (m + 1) (s - 1) := by
    apply (scoreLow_mono D Sc (by simp; omega) _).trans hlow
    rw [positionedScore_dots hl]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    omega
  by_cases hr : IsReduced t.length (a :: σ)
  · set σ' := canWord t.length (sadj t.length a * w)
    have hb : BraidEquiv (a :: σ) σ' :=
      braidEquiv_of_isReduced hr (isReduced_canWord t.length _) (by simp [σ, σ'])
    have h' := sChain_of_braid (l.map PG.dot) hb hv rfl h₀
    refine WeightedApprox.mem D Sc (weighted_braid_move D Sc (l.map PG.dot) rfl hb hv h₀ h') hlow'
      (Submodule.subset_span ⟨l, hs, hl, sadj t.length a * w, ?_, ?_, h', rfl⟩)
    all_goals
      have h2 : wordProd t.length (a :: σ) = sadj t.length a * w := by simp [σ]
      have := hr.2
      rw [h2, List.length_cons] at this
      omega
  · obtain ⟨σ', hb, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hv hr
    have h' := sChain_of_braid (l.map PG.dot) hb hv rfl h₀
    refine WeightedApprox.mem D Sc (weighted_braid_move D Sc (l.map PG.dot) rfl hb hv h₀ h') hlow' (hlow' ?_)
    have e₂ : l.map PG.dot ++ cw σ' = l.map PG.dot ++ cw σ' ++ [] := by simp
    rw [cl_eq_cl e₂ h' (e₂ ▸ h')]
    refine boundedScore_le_scoreLow D Sc ?_ ?_
      (cl_mem_boundedScore_of_hasRepeat D Sc (l.map PG.dot) [] rfl
        (hb.validWord_iff.mp hv) hrep (e₂ ▸ h'))
    · have := hb.length_eq
      simp at this ⊢; omega
    · rw [hb.length_eq]
      simp [positionedScore]


theorem nil_mem_weightedNF {t t' : List I} (h : SChain t (pl t []) t') (m : ℕ)
    {s : ℤ} (hs : s ≤ 0) : cl D Sc t t' [] h ∈ WeightedNF D Sc t t' m s := by
  have hc : canWord t.length 1 = [] :=
    List.eq_nil_of_length_eq_zero (by rw [length_canWord, length_eq_zero_iff])
  have e : ([] : List PG) = ([] : List ℕ).map PG.dot ++ cw (canWord t.length 1) := by simp [hc]
  refine Submodule.subset_span ⟨[], List.Pairwise.nil, by simp, 1, ?_, ?_, e ▸ h, ?_⟩
  · simp [length_eq_zero_iff.mpr rfl]
  · simpa [length_eq_zero_iff.mpr rfl] using hs
  · exact (cl_eq_cl e h _).symm

theorem cl_mem_weightedNF {t : List I} {m : ℕ}
    (hlow : ∀ t' s, ScoreLow D Sc t t' m s ≤ WeightedNF D Sc t t' m s)
    (hprev : ∀ j < m, ∀ t' s, BoundedScore D Sc t t' j s ≤ WeightedNF D Sc t t' j s)
    (gs : List PG) :
    ∀ {t'} (h : SChain t (pl t gs) t'), crossCount gs ≤ m →
      cl D Sc t t' gs h ∈ WeightedNF D Sc t t' m (positionedScore t.length gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t' h _
    exact nil_mem_weightedNF D Sc h m (by simp [positionedScore])
  | append_singleton gs g ih =>
    intro t' h hc
    simp only [crossCount_append, crossCount_cons, crossCount_nil, add_zero] at hc
    by_cases hfit : g.pos + g.width ≤ (tgt t gs).length
    · rw [cl_append]
      cases g with
      | dot p =>
        have hp : p < t.length := by simpa [PG.pos, PG.width] using hfit
        rw [positionedScore_append, positionedScore_dot hp]
        exact weighted_nf_comp_dot D Sc (hlow _ _) (by simpa using hp) _
          (ih (sChain_pl t gs) (by simp [PG.isCross] at hc ⊢; omega))
      | cross a =>
        have ha : a + 1 < t.length := by simp only [PG.pos, PG.width, length_tgt] at hfit; omega
        rw [positionedScore_append, positionedScore_cross ha]
        simp only [← sub_eq_add_neg]
        simp only [PG.isCross] at hc
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact weighted_nf_comp_cross D Sc (hlow _ _) (by simpa using ha) _
          (hprev m' (by omega) _ _ (cl_mem_boundedScore D Sc _ (by omega) le_rfl))
    · have e : pl t (gs ++ [g]) = pl t gs := by
        rw [pl_append]; simp [ld_eq_nil (show (tgt t gs).length < g.pos + g.width by omega)]
      have h' : SChain t (pl t gs) t' := e ▸ h
      rw [cl_congr D Sc h h' (by rw [e])]
      have hn : ¬g.pos + g.width ≤ t.length := by simpa using hfit
      have he : positionedScore t.length [g] = 0 := by simp [positionedScore, hn]
      rw [positionedScore_append, he, add_zero]
      exact ih h' (by omega)

theorem scoreLow_succ_le_boundedScore (t t' : List I) (m : ℕ) (s : ℤ) :
    ScoreLow D Sc t t' (m + 1) s ≤ BoundedScore D Sc t t' m s :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, hd, e⟩ =>
    ⟨gs, hg, Nat.lt_succ_iff.mp hc, hd, e⟩

/-- Affine straightening preserves the lower bound on dots minus crossings.
No SKM injectivity or cyclotomic faithfulness is assumed. -/
theorem boundedScore_le_weightedNF (t : List I) (m : ℕ) (t' : List I) (s : ℤ) :
    BoundedScore D Sc t t' m s ≤ WeightedNF D Sc t t' m s := by
  induction m using Nat.strong_induction_on generalizing t' s with
  | _ m ihm =>
    have hlow : ∀ t' s, ScoreLow D Sc t t' m s ≤ WeightedNF D Sc t t' m s := by
      intro t' s
      rcases m with _ | j
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨gs, h, hc, hs, rfl⟩
        exact absurd hc (Nat.not_lt_zero _)
      · exact (scoreLow_succ_le_boundedScore D Sc t t' j s).trans
          ((ihm j (by omega) t' s).trans (weightedNF_mono D Sc (by omega) le_rfl))
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨gs, h, hc, hs, rfl⟩
    exact weightedNF_mono D Sc le_rfl hs
      (cl_mem_weightedNF D Sc hlow (fun j hj t' s => ihm j hj t' s) gs h hc)

/-- A positioned word has a canonical PBW expansion with no loss of score. -/
theorem word_mem_weightedNF {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h ∈
      WeightedNF D Sc t t' (crossCount gs) (positionedScore t.length gs) :=
  boundedScore_le_weightedNF D Sc _ _ _ _
    (cl_mem_boundedScore D Sc h le_rfl le_rfl)

end OddMath.QuiverHecke
