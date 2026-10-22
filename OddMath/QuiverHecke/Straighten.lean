/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PositionalRelations

/-!
# Local moves in context

The positioned relations of `PositionalRelations`, placed between arbitrary words below and
above. `Low t t' n` is the span of the classes of words with fewer than `n` crossings; a move
`x ≈ y` modulo `Low` says `x ∈ k ∙ y ⊔ Low`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

theorem sChain_append_of {t t₁ t' : List I} {Q R : List PG} (h₁ : SChain t (pl t Q) t₁)
    (h₂ : SChain t₁ (pl t₁ R) t') : SChain t (pl t (Q ++ R)) t' := by
  rw [pl_append, tgt_eq h₁]; exact h₁.append h₂

theorem cl_comp {t t₁ t' : List I} (Q R : List PG) (h₁ : SChain t (pl t Q) t₁)
    (h₂ : SChain t₁ (pl t₁ R) t') :
    cl D Sc t t₁ Q h₁ ≫ cl D Sc t₁ t' R h₂ = cl D Sc t t' (Q ++ R) (sChain_append_of h₁ h₂) := by
  obtain rfl := tgt_eq h₁
  rw [cl_append]

/-- Words with fewer than `n` crossings. -/
def Low (t t' : List I) (n : ℕ) :
    Submodule k ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :=
  Submodule.span k {f | ∃ gs h, crossCount gs < n ∧ cl D Sc t t' gs h = f}

theorem cl_mem_low {t t' : List I} {gs : List PG} (h : SChain t (pl t gs) t') {n : ℕ}
    (hn : crossCount gs < n) : cl D Sc t t' gs h ∈ Low D Sc t t' n :=
  Submodule.subset_span ⟨gs, h, hn, rfl⟩

theorem low_mono {t t' : List I} {m n : ℕ} (h : m ≤ n) :
    Low D Sc t t' m ≤ Low D Sc t t' n :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, e⟩ => ⟨gs, hg, lt_of_lt_of_le hc h, e⟩

theorem filt_le_low {t t' : List I} {m n : ℕ} (h : m < n) :
    Filt D Sc t t' m ≤ Low D Sc t t' n :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, e⟩ => ⟨gs, hg, lt_of_le_of_lt hc h, e⟩

theorem low_le_filt {t t' : List I} (n : ℕ) :
    Low D Sc t t' (n + 1) ≤ Filt D Sc t t' n :=
  Submodule.span_mono fun _ ⟨gs, hg, hc, e⟩ => ⟨gs, hg, Nat.lt_succ_iff.mp hc, e⟩

/-- Composing a member of `Filt` with words below and above. -/
theorem comp_filt_comp {t t₁ t₂ t' : List I} (Q R : List PG) (h₁ : SChain t (pl t Q) t₁)
    (h₂ : SChain t₂ (pl t₂ R) t') {j : ℕ} {f : (pres D Sc).obj (ob D t₁) ⟶ (pres D Sc).obj (ob D t₂)}
    (hf : f ∈ Filt D Sc t₁ t₂ j) :
    cl D Sc t t₁ Q h₁ ≫ f ≫ cl D Sc t₂ t' R h₂ ∈
      Filt D Sc t t' (crossCount Q + j + crossCount R) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨gs, hg, hc, rfl⟩ := hx
    rw [cl_comp, cl_comp]
    exact cl_mem_filt D Sc _ (by simp only [crossCount_append]; omega)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ c hx

/-- A local move: if `M` agrees with `c • M'` up to words with at most `j` crossings, then
so does `Q ++ M ++ R` with `Q ++ M' ++ R`. -/
theorem move_ctx {t t₁ t₂ t' : List I} (Q M M' R : List PG) (c : k) {j : ℕ}
    (hQ : SChain t (pl t Q) t₁) (hR : SChain t₂ (pl t₂ R) t')
    (hM : SChain t₁ (pl t₁ M) t₂) (hM' : SChain t₁ (pl t₁ M') t₂)
    (hmove : cl D Sc t₁ t₂ M hM - c • cl D Sc t₁ t₂ M' hM' ∈ Filt D Sc t₁ t₂ j)
    (h : SChain t (pl t (Q ++ M ++ R)) t') (h' : SChain t (pl t (Q ++ M' ++ R)) t') :
    cl D Sc t t' (Q ++ M ++ R) h - c • cl D Sc t t' (Q ++ M' ++ R) h' ∈
      Filt D Sc t t' (crossCount Q + j + crossCount R) := by
  have e₁ : cl D Sc t t' (Q ++ M ++ R) h =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M hM ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  have e₂ : cl D Sc t t' (Q ++ M' ++ R) h' =
      cl D Sc t t₁ Q hQ ≫ cl D Sc t₁ t₂ M' hM' ≫ cl D Sc t₂ t' R hR := by
    rw [cl_comp, cl_comp]; simp only [List.append_assoc]
  rw [e₁, e₂]
  convert comp_filt_comp D Sc Q R hQ hR hmove using 1
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul]

/-! ## Positions and widths -/

/-- The leftmost strand of a positioned generator. -/
def PG.pos : PG → ℕ
  | .dot p => p
  | .cross a => a

/-- The number of strands of a positioned generator. -/
def PG.width : PG → ℕ
  | .dot _ => 1
  | .cross _ => 2

theorem exists_split (g : PG) (n₀ : ℕ) (t : List I) (h₀ : n₀ ≤ g.pos)
    (hg : g.pos + g.width ≤ n₀ + t.length) :
    ∃ l s r, t = l ++ Shape.dom s ++ r ∧ PG.ofShape s (n₀ + l.length) = g ∧
      n₀ + l.length = g.pos ∧ (Shape.dom s).length = g.width := by
  cases g with
  | dot p =>
    simp only [PG.pos, PG.width] at h₀ hg
    obtain ⟨x, hx⟩ : ∃ x, t.drop (p - n₀) = x :: t.drop (p - n₀ + 1) := by
      refine ⟨t[p - n₀]'(by omega), ?_⟩
      rw [List.drop_eq_getElem_cons]
    refine ⟨t.take (p - n₀), .dot x, t.drop (p - n₀ + 1), ?_, ?_, ?_, rfl⟩
    · conv_lhs => rw [← List.take_append_drop (p - n₀) t, hx]
      simp [Shape.dom]
    · simp only [PG.ofShape, List.length_take]
      congr 1; omega
    · simp [PG.pos]; omega
  | cross a =>
    simp only [PG.pos, PG.width] at h₀ hg
    obtain ⟨x, y, hx⟩ : ∃ x y, t.drop (a - n₀) = x :: y :: t.drop (a - n₀ + 2) := by
      refine ⟨t[a - n₀]'(by omega), t[a - n₀ + 1]'(by omega), ?_⟩
      rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
    refine ⟨t.take (a - n₀), .cross x y, t.drop (a - n₀ + 2), ?_, ?_, ?_, rfl⟩
    · conv_lhs => rw [← List.take_append_drop (a - n₀) t, hx]
      simp [Shape.dom]
    · simp only [PG.ofShape, List.length_take]
      congr 1; omega
    · simp [PG.pos]; omega

/-- Far commutation: generators at disjoint positions commute up to a sign. -/
theorem far_swap {t₁ t₂ : List I} (g h : PG) (hgh : g.pos + g.width ≤ h.pos)
    (hh : h.pos + h.width ≤ t₁.length) (h₁ : SChain t₁ (pl t₁ [g, h]) t₂)
    (h₂ : SChain t₁ (pl t₁ [h, g]) t₂) :
    ∃ c : k, c * c = 1 ∧ cl D Sc t₁ t₂ [g, h] h₁ = c • cl D Sc t₁ t₂ [h, g] h₂ := by
  obtain ⟨l, sg, r, rfl, hsg, hl, hw⟩ := exists_split g 0 t₁ (Nat.zero_le _) (by omega)
  obtain ⟨m, sh, v, rfl, hsh, hm, hw'⟩ := exists_split h (l ++ sg.dom).length r
    (by simp; omega) (by simp at hh ⊢; omega)
  simp only [zero_add] at hsg
  subst hsg hsh
  have e : l ++ sg.dom ++ (m ++ sh.dom ++ v) = l ++ sg.dom ++ m ++ sh.dom ++ v := by
    simp
  have e' : (l ++ sg.dom).length + m.length = (l ++ sg.dom ++ m).length := by simp; omega
  revert h₁ h₂
  rw [e, e']
  intro h₁ h₂
  have ht : tgt (l ++ sg.dom ++ m ++ sh.dom ++ v)
      [PG.ofShape sg l.length, PG.ofShape sh (l ++ sg.dom ++ m).length] =
        l ++ sg.cod ++ m ++ sh.cod ++ v := by
    cases sg <;> cases sh <;>
      simp [PG.act, PG.ofShape, Shape.dom, Shape.cod, List.take_append, List.drop_append]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h₁
  refine ⟨_, ?_, cl_interchange D Sc l m v sg sh h₁ h₂⟩
  unfold zsign; split_ifs <;> simp

theorem exists_split_cross {t : List I} {a : ℕ} (ha : a + 1 < t.length) :
    ∃ l x y r, t = l ++ [x, y] ++ r ∧ l.length = a := by
  obtain ⟨l, s, r, rfl, hs, hl, hw⟩ := exists_split (.cross a) 0 t (Nat.zero_le _)
    (by simp [PG.pos, PG.width]; omega)
  cases s with
  | dot x => simp [PG.ofShape] at hs
  | cross x y => exact ⟨l, x, y, r, rfl, by simpa [PG.pos] using hl⟩

/-- (1.7) at a position of any word. -/
theorem cross_cross_at {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h : SChain t₁ (pl t₁ [.cross a, .cross a]) t₂) :
    cl D Sc t₁ t₂ [.cross a, .cross a] h ∈ Filt D Sc t₁ t₂ 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
  have ht : tgt (l ++ [x, y] ++ r) [.cross l.length, .cross l.length] = l ++ [x, y] ++ r := by
    simp [PG.act]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h
  exact cross_cross_mem D Sc l r x y h

/-- (1.8), left, at a position of any word. -/
theorem slide_left_at {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.dot a, .cross a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.cross a, .dot (a + 1)]) t₂) :
    ∃ c : k, c * c = 1 ∧ cl D Sc t₁ t₂ [.dot a, .cross a] h₁ -
      c • cl D Sc t₁ t₂ [.cross a, .dot (a + 1)] h₂ ∈ Filt D Sc t₁ t₂ 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
  have ht : tgt (l ++ [x, y] ++ r) [.dot l.length, .cross l.length] = l ++ [y, x] ++ r := by
    simp [PG.act]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h₁
  exact ⟨_, by unfold zsign; split_ifs <;> simp, slide_left D Sc l r x y h₁ h₂⟩

/-- (1.8), right, at a position of any word. -/
theorem slide_right_at {t₁ t₂ : List I} {a : ℕ} (ha : a + 1 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.cross a, .dot a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.dot (a + 1), .cross a]) t₂) :
    ∃ c : k, c * c = 1 ∧ cl D Sc t₁ t₂ [.cross a, .dot a] h₁ -
      c • cl D Sc t₁ t₂ [.dot (a + 1), .cross a] h₂ ∈ Filt D Sc t₁ t₂ 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
  have ht : tgt (l ++ [x, y] ++ r) [.cross l.length, .dot l.length] = l ++ [y, x] ++ r := by
    simp [PG.act]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h₁
  exact ⟨_, by unfold zsign; split_ifs <;> simp, slide_right D Sc l r x y h₁ h₂⟩

/-- (1.9) at a position of any word. -/
theorem braid_at {t₁ t₂ : List I} {a : ℕ} (ha : a + 2 < t₁.length)
    (h₁ : SChain t₁ (pl t₁ [.cross a, .cross (a + 1), .cross a]) t₂)
    (h₂ : SChain t₁ (pl t₁ [.cross (a + 1), .cross a, .cross (a + 1)]) t₂) :
    cl D Sc t₁ t₂ [.cross a, .cross (a + 1), .cross a] h₁ -
      cl D Sc t₁ t₂ [.cross (a + 1), .cross a, .cross (a + 1)] h₂ ∈ Filt D Sc t₁ t₂ 0 := by
  obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross (t := t₁) (a := a) (by omega)
  obtain ⟨z, r, rfl⟩ : ∃ z r', r = z :: r' := by
    cases r with
    | nil => simp at ha
    | cons z r' => exact ⟨z, r', rfl⟩
  have e : l ++ [x, y] ++ z :: r = l ++ [x, y, z] ++ r := by simp
  revert h₁ h₂
  rw [e]
  intro h₁ h₂
  have ht : tgt (l ++ [x, y, z] ++ r) [.cross l.length, .cross (l.length + 1), .cross l.length] =
      l ++ [z, y, x] ++ r := by
    simp [PG.act, List.take_append, List.drop_append]
  obtain rfl : _ = t₂ := ht ▸ tgt_eq h₁
  exact braid_mem D Sc l r x y z h₁ h₂

end OddMath.QuiverHecke
