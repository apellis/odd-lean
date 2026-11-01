import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyMap

/-! # Entries of the actual cyclotomic matrix ideal

The reverse matrix-ideal comparison needed by AppendMackeySource, section 4.
Every entry of an element of the actual Hn cyclotomic ideal belongs to the
ordinary cyclotomic morphism ideal. The proof uses actual finite-support
single matrices and composition closure; no tensor flatness or quotient
presentation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ)

private def cyclotomicEntrySpan : Submodule k (Hn D Sc (n + 1)) :=
  Submodule.span k {x | ∃ (t s : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t),
    f ∈ cycHom D Sc a s.val t.val ∧ x = FiniteHomMatrix.single t s f}

private theorem entrySpan_mul_left (b : Hn D Sc (n + 1))
    {x : Hn D Sc (n + 1)} (hx : x ∈ cyclotomicEntrySpan D Sc a n) :
    b * x ∈ cyclotomicEntrySpan D Sc a n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, s, f, hf, rfl⟩ := hx
    induction b using FiniteHomMatrix.induction with
    | hz =>
      rw [zero_mul]
      exact Submodule.zero_mem _
    | ha b c hb hc =>
      rw [add_mul]
      exact Submodule.add_mem _ hb hc
    | hs r q g =>
      by_cases h : q = t
      · subst t
        rw [FiniteHomMatrix.single_mul_single]
        exact Submodule.subset_span ⟨r, s, f ≫ g, cycHom_comp_right D Sc hf g, rfl⟩
      · rw [FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
        exact Submodule.zero_mem _
  | zero =>
    rw [mul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

private theorem entrySpan_mul_right {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicEntrySpan D Sc a n) (b : Hn D Sc (n + 1)) :
    x * b ∈ cyclotomicEntrySpan D Sc a n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, s, f, hf, rfl⟩ := hx
    induction b using FiniteHomMatrix.induction with
    | hz =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | ha b c hb hc =>
      rw [mul_add]
      exact Submodule.add_mem _ hb hc
    | hs r q g =>
      by_cases h : s = r
      · subst r
        rw [FiniteHomMatrix.single_mul_single]
        exact Submodule.subset_span ⟨t, q, g ≫ f, cycHom_comp_left D Sc g hf, rfl⟩
      · rw [FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
        exact Submodule.zero_mem _
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

omit [Fintype I] in
private theorem cyclotomicGenerator_mem_entrySpan (w : Word I (n + 1)) :
    cyclotomicGenerator D Sc a w ∈ cyclotomicEntrySpan D Sc a n := by
  rcases w with ⟨l, hl⟩
  cases l with
  | nil => simp at hl
  | cons j l =>
    change FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
      (⟨j :: l, hl⟩ : Word I (n + 1))
      (⟨j :: l, hl⟩ : Word I (n + 1)) (firstDotPoly D Sc a j l) ∈ _
    apply Submodule.subset_span
    refine ⟨⟨j :: l, hl⟩, ⟨j :: l, hl⟩, firstDotPoly D Sc a j l, ?_, rfl⟩
    apply Submodule.subset_span
    exact ⟨j, l, 𝟙 _, 𝟙 _, by simp⟩

private theorem entrySpan_entry {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicEntrySpan D Sc a n) (t s : Word I (n + 1)) :
    x (t, s) ∈ cycHom D Sc a s.val t.val := by
  let : DecidableEq (Word I (n + 1)) := Classical.decEq _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, f, hf, rfl⟩ := hx
    by_cases ht : t = u
    · subst t
      by_cases hs : s = w
      · subst s
        simpa only [FiniteHomMatrix.single, DFinsupp.single_eq_same] using hf
      · have h : (u, s) ≠ (u, w) := fun h => hs (congrArg Prod.snd h)
        have hz : (FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
            u w f) (u, s) = 0 := DFinsupp.single_eq_of_ne h
        rw [hz]
        exact Submodule.zero_mem _
    · have h : (t, s) ≠ (u, w) := fun h => ht (congrArg Prod.fst h)
      have hz : (FiniteHomMatrix.single (obj := wordObj D Sc (n := n + 1))
          u w f) (t, s) = 0 := DFinsupp.single_eq_of_ne h
      rw [hz]
      exact Submodule.zero_mem _
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    change x (t, s) + y (t, s) ∈ _
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    change c • x (t, s) ∈ _
    exact Submodule.smul_mem _ c hx

/-- Each actual Hn ideal entry lies in the corresponding ordinary morphism ideal. -/
theorem cyclotomicIdeal_entry_mem_cycHom {x : Hn D Sc (n + 1)}
    (hx : x ∈ cyclotomicIdeal D Sc a n) (t s : Word I (n + 1)) :
    x (t, s) ∈ cycHom D Sc a s.val t.val := by
  have hs : x ∈ cyclotomicEntrySpan D Sc a n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, b, rfl⟩ := hy
      exact entrySpan_mul_right D Sc a n (cyclotomicGenerator_mem_entrySpan D Sc a n w) b
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul b x _ hx =>
      change b * x ∈ _
      exact entrySpan_mul_left D Sc a n b hx
  exact entrySpan_entry D Sc a n hs t s

/-- A single matrix belongs to the actual ideal exactly when its morphism does. -/
theorem single_mem_cyclotomicIdeal_iff (t s : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t s f ∈ cyclotomicIdeal D Sc a n ↔
      f ∈ cycHom D Sc a s.val t.val := by
  constructor
  · intro hf
    simpa only [FiniteHomMatrix.single, DFinsupp.single_eq_same] using
      cyclotomicIdeal_entry_mem_cycHom D Sc a n hf t s
  · exact single_mem_cyclotomicIdeal D Sc a n t s

end OddMath.QuiverHecke

