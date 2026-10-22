/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.SpanMatchings
import OddMath.SKM.SpanCapTrack
import OddMath.SKM.SpanClosed
import OddMath.SKM.LaurentianHoms
import OddMath.SKM.K0Relations
import StringDiagrams.Karoubi.KrullSchmidt

/-!
# Indecomposable summands of `Q^m Π^a 1_λ` (base case of the width induction)

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, the case of width
zero. By Theorem 8.1 the endomorphisms of `1_λ` are the images of the bubble algebra `SYM`,
whose generators all have positive degree; so `End(1_λ)` has nothing in negative degree and
only scalars in degree zero. Hence `Q^m Π^a 1_λ` is zero or indecomposable, and it is the only
indecomposable summand of itself up to isomorphism.

* `endOne_mem_bubbleSpan`: Theorem 8.1 with empty boundary, `End(1_λ) = β_λ(SYM)`.
* `homDeg_endOne_eq_bot`, `homDeg_endOne_zero`: `End(1_λ)` vanishes in negative degrees and
  is `k · 1` in degree zero.
* `idem_shifted_one`: an even degree-zero idempotent of `Q^m Π^a 1_λ` is `0` or `1`.
* `iso_of_retract_one`: an indecomposable retract of `Q^m Π^a 1_λ` in `U̇` is isomorphic to it;
  `cls_eq_of_retract_one`: its class in the Grothendieck ring is `[Q^m Π^a 1_λ]`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits run Iso Reduced)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [Field k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Placing an endomorphism of `1_μ` with no strands around it does nothing. -/
theorem bubAt_nil (μ : X) : bubAt D Sc μ [] = LinearMap.id :=
  hom_ext_cl _ _ fun L => by rw [bubAt_cl, map_whL_nil_nil]; rfl

/-- **BE2 Theorem 8.1 for the empty boundary**: every endomorphism of `1_μ` is a linear
combination of products of bubbles. -/
theorem endOne_mem_bubbleSpan (μ : X)
    (f : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])) :
    (f : End ((pres D Sc).obj (ob D μ []))) ∈ bubbleSpan cs μ := by
  have h := theorem_8_1_nil_bottom (cs := cs) μ [] {[]}
    (by
      rintro E rfl
      exact ⟨⟨by simp [Fits], rfl⟩, by simp [Reduced, Chord.xps]⟩)
    (by
      intro E hE _
      refine ⟨[], rfl, ?_⟩
      have h1 : (run flipL E).map Prod.snd = [] := by rw [← foldl_chStep_eq]; exact hE.2
      rw [List.map_eq_nil_iff] at h1
      rw [h1]
      exact Iso.refl _)
    (fun _ _ => (0, 0)) (by rintro E rfl j hj; simp [leftEnds, Chord.run] at hj)
    (fun _ _ => []) (by rintro E rfl n; exact ⟨rfl, by simp [leftEnds, Chord.run, DMove.dotPts]⟩)
  have hf : f ∈ diagBubSpan D Sc cs μ [] [] (decoratedFamily {[]} fun _ _ => []) := by
    rw [h]
    trivial
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (bubbleSpan cs μ))).2 ?_ hf
  rintro _ ⟨C, ⟨E, rfl, n, rfl⟩, β, hβ, rfl⟩
  simp only [dmLay, xev_nil_eq_id, bubAt_nil, LinearMap.id_apply, Category.id_comp]
  exact hβ

variable (sy : Symmetrizer D)

/-- The images of the words in the generators of `SYM` span `End(1_μ)`. -/
theorem span_betaSYM_words (μ : X) :
    Submodule.span k (Set.range fun l : List (SYMGen D) =>
      betaSYM cs μ ((l.map (SYM.ι D k)).prod)) = ⊤ := by
  change Submodule.span k (Set.range fun l : List (SYMGen D) =>
    (betaSYM cs μ).toLinearMap ((l.map (SYM.ι D k)).prod)) = ⊤
  rw [Set.range_comp' (betaSYM cs μ).toLinearMap (fun l : List (SYMGen D) =>
      (l.map (SYM.ι D k)).prod), Submodule.span_image, SYM.span_words, Submodule.map_top,
    eq_top_iff]
  intro f _
  have hf := endOne_mem_bubbleSpan cs μ f
  rw [← betaSYM_range cs μ] at hf
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, hx⟩

/-- The integer-degree pieces of `End(1_μ)` are spanned by the images of the words of that
degree in the generators of `SYM`. -/
theorem homDeg_endOne_eq_span (hc : Sc.Homogeneous) (μ : X) (n : ℤ) :
    (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) n =
      Submodule.span k ((fun l : List (SYMGen D) => betaSYM cs μ ((l.map (SYM.ι D k)).prod)) ''
        {l | (l.map (symGenDegree D sy)).sum = n}) :=
  GradedSpanning.component_eq_span _ (isInternal_homDeg_gdeg D sy Sc hc _ _) _ _
    (fun l => MatchingBasisChoice.beta_word_mem_gdeg sy cs μ l) (span_betaSYM_words cs μ) n

/-- A nonempty word in the generators of `SYM` has positive degree. -/
theorem symGenDegree_sum_pos {l : List (SYMGen D)} (hl : l ≠ []) :
    0 < (l.map (symGenDegree D sy)).sum :=
  List.sum_pos _ (fun x hx => by
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
    exact symGenDegree_pos sy g) (by simpa using hl)

include cs in
/-- `End(1_μ)` vanishes in negative degrees. -/
theorem homDeg_endOne_eq_bot (hc : Sc.Homogeneous) (μ : X) {n : ℤ} (hn : n < 0) :
    (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) n = ⊥ := by
  rw [homDeg_endOne_eq_span cs sy hc μ, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  rcases eq_or_ne l [] with rfl | hne
  · simp at hl
    omega
  · have h2 : (l.map (symGenDegree D sy)).sum = n := hl
    have := symGenDegree_sum_pos sy hne
    omega

include cs in
/-- The degree-zero part of `End(1_μ)` consists of the scalar multiples of the identity. -/
theorem homDeg_endOne_zero (hc : Sc.Homogeneous) (μ : X)
    {f : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) 0) :
    ∃ c : k, f = c • 𝟙 _ := by
  rw [homDeg_endOne_eq_span cs sy hc μ] at hf
  have hs : (fun l : List (SYMGen D) => betaSYM cs μ ((l.map (SYM.ι D k)).prod)) ''
      {l | (l.map (symGenDegree D sy)).sum = 0} ⊆ {𝟙 _} := by
    rintro _ ⟨l, hl, rfl⟩
    rcases eq_or_ne l [] with rfl | hne
    · simp only [List.map_nil, List.prod_nil, map_one, Set.mem_singleton_iff]
      rfl
    · have h2 : (l.map (symGenDegree D sy)).sum = 0 := hl
      have := symGenDegree_sum_pos sy hne
      omega
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Submodule.span_mono hs hf)
  exact ⟨c, hc.symm⟩

/-! ### `Q^m Π^a 1_μ` in the completed category -/

section Completed

open K0Relations GradedSupercategory StringDiagrams.KrullSchmidt

variable (hc : Sc.Homogeneous)

include cs in
/-- An even degree-zero idempotent of `Q^m Π^a 1_μ` is `0` or `1`. -/
theorem idem_shifted_one (μ : X) (hs : wt D μ [] = μ) (m : ℤ) (a : ZMod 2)
    (e : shifted Sc sy hc μ μ [] hs m a ⟶ shifted Sc sy hc μ μ [] hs m a) (he : e ≫ e = e) :
    e = 0 ∨ e = 𝟙 _ := by
  have h1 := e.1.2
  change e.1.1 ∈ degree (R := k) (word Sc sy hc μ μ [] hs) (word Sc sy hc μ μ [] hs)
    (0 + (m - m)) at h1
  rw [sub_self, add_zero] at h1
  obtain ⟨c, hc'⟩ : ∃ c : k, e.1.1 = c • 𝟙 (word Sc sy hc μ μ [] hs) := by
    exact homDeg_endOne_zero cs sy hc μ h1
  have hval : ∀ f g : shifted Sc sy hc μ μ [] hs m a ⟶ shifted Sc sy hc μ μ [] hs m a,
      f.1.1 = g.1.1 → f = g := fun f g h => Subtype.ext (Subtype.ext h)
  have hee : e.1.1 ≫ e.1.1 = e.1.1 := congrArg (fun f => f.1.1) he
  by_cases h0 : 𝟙 (word Sc sy hc μ μ [] hs) = 0
  · left
    refine hval _ _ ?_
    exact hc'.trans (((congrArg (c • ·) h0).trans (smul_zero c)).trans rfl)
  rw [show e.1.1 = c • 𝟙 _ from hc'] at hee
  rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul, ← sub_eq_zero,
    ← sub_smul, smul_eq_zero] at hee
  rcases hee with hcc | hcc
  · have : c = 0 ∨ c = 1 := by
      have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hcc
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases this with rfl | rfl
    · left
      refine hval _ _ ?_
      exact hc'.trans ((zero_smul _ _).trans rfl)
    · right
      refine hval _ _ ?_
      exact hc'.trans (one_smul _ _)
  · exact absurd hcc h0

/-- If the only idempotents of `W` are `0` and `1`, the same holds for its image under a fully
faithful functor. -/
theorem idem_map_of_idem {C E : Type*} [Category C] [Category E] [Preadditive C] [Preadditive E]
    (F : C ⥤ E) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] {W : C}
    (h : ∀ e : W ⟶ W, e ≫ e = e → e = 0 ∨ e = 𝟙 W) (e : F.obj W ⟶ F.obj W) (he : e ≫ e = e) :
    e = 0 ∨ e = 𝟙 _ := by
  obtain ⟨e, rfl⟩ := F.map_surjective e
  rcases h e (F.map_injective (by rw [F.map_comp, he])) with rfl | rfl
  · exact Or.inl (F.map_zero _ _)
  · exact Or.inr (F.map_id _)

/-- If the only idempotents of `W` are `0` and `1`, every indecomposable retract of `W` is
isomorphic to `W`. -/
theorem iso_of_retract_of_idem {C : Type*} [Category C] [Preadditive C] {W Z : C}
    (h : ∀ e : W ⟶ W, e ≫ e = e → e = 0 ∨ e = 𝟙 W) (hZ : IsIndec Z)
    (ι : Z ⟶ W) (π : W ⟶ Z) (hιπ : ι ≫ π = 𝟙 Z) : Nonempty (Z ≅ W) := by
  have hidem : (π ≫ ι) ≫ π ≫ ι = π ≫ ι := by
    rw [Category.assoc, ← Category.assoc ι, hιπ, Category.id_comp]
  rcases h _ hidem with h0 | h1
  · refine absurd ?_ hZ.1
    rw [Limits.IsZero.iff_id_eq_zero]
    calc 𝟙 Z = (ι ≫ π) ≫ (ι ≫ π) := by rw [hιπ, Category.id_comp]
      _ = ι ≫ (π ≫ ι) ≫ π := by simp only [Category.assoc]
      _ = 0 := by rw [h0]; simp
  · exact ⟨⟨ι, π, hιπ, h1⟩⟩


variable {sy hc} in
include cs in
/-- **Width zero (BE2, proof of Theorem 11.7)**: an indecomposable retract of `Q^m Π^a 1_μ` in
`U̇` is isomorphic to `Q^m Π^a 1_μ`. -/
theorem iso_of_retract_one (μ : X) (hs : wt D μ [] = μ) (m : ℤ) (a : ZMod 2)
    {Z : weight Sc sy hc μ ⟶ weight Sc sy hc μ} (hZ : IsIndec Z)
    (ι : Z ⟶ completed Sc sy hc μ μ [] hs m a) (π : completed Sc sy hc μ μ [] hs m a ⟶ Z)
    (h : ι ≫ π = 𝟙 Z) : Nonempty (Z ≅ completed Sc sy hc μ μ [] hs m a) :=
  iso_of_retract_of_idem (idem_map_of_idem (inclusion Sc sy hc μ μ)
    (idem_shifted_one cs sy hc μ hs m a)) hZ ι π h

variable {sy hc} in
include cs in
/-- The class of an indecomposable retract of `Q^m Π^a 1_μ` is `[Q^m Π^a 1_μ]`. -/
theorem cls_eq_of_retract_one (μ : X) (hs : wt D μ [] = μ) (m : ℤ) (a : ZMod 2)
    {Z : weight Sc sy hc μ ⟶ weight Sc sy hc μ} (hZ : IsIndec Z)
    (ι : Z ⟶ completed Sc sy hc μ μ [] hs m a) (π : completed Sc sy hc μ μ [] hs m a ⟶ Z)
    (h : ι ≫ π = 𝟙 Z) : MulOpposite.op (K₀Ring.mk Z) = cls Sc sy hc μ μ [] hs m a := by
  obtain ⟨e⟩ := iso_of_retract_one cs μ hs m a hZ ι π h
  exact congrArg MulOpposite.op (K₀Ring.mk_eq_mk_of_iso e)

variable {sy hc} in
include cs in
/-- `Q^m Π^a 1_μ` is indecomposable or zero. -/
theorem isIndec_or_isZero_one (μ : X) (hs : wt D μ [] = μ) (m : ℤ) (a : ZMod 2) :
    IsIndec (completed Sc sy hc μ μ [] hs m a) ∨
      Limits.IsZero (completed Sc sy hc μ μ [] hs m a) := by
  by_cases h : Limits.IsZero (completed Sc sy hc μ μ [] hs m a)
  · exact Or.inr h
  · exact Or.inl ⟨h, idem_map_of_idem (inclusion Sc sy hc μ μ)
      (idem_shifted_one cs sy hc μ hs m a)⟩

end Completed

end OddMath.SKM
