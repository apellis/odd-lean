/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianHoms
import OddMath.SKM.GradedExpansion
import OddMath.SKM.SpanBubbleProd
import OddMath.SKM.DimensionComponents
import OddMath.SKM.Envelope
import OddMath.SKM.NilKrullSchmidt.Graded

/-!
# The bubble filtration of the super Kac–Moody Hom-spaces

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §11. For an arbitrary
set of colours the integer-degree pieces of the Hom-spaces of `𝔘(𝔤)` need not be finite
dimensional: the bubbles of a fixed degree span an infinite-dimensional space when infinitely
many colours have the same symmetrizer value. The Krull–Schmidt input of Theorem 11.7 holds
nevertheless. The two-sided filtration by the span of the 2-morphisms that factor through a
closed diagram (in the rightmost region) of degree at least `d` is multiplicative, by the
bubble slides of Theorem 8.1 (in the form `comp_bubAt`), and in each fixed degree it vanishes
in high index, by the lower degree bound of the spanning set of Theorem 8.1. Modulo its first
step, each degree piece is spanned by the finitely many decorated diagrams of that degree with
no bubbles. This gives a `GradedNilFiltration` without any finiteness assumption on the
colours, and with it the Laurent bases of §11.

The lower degree bound `hom_boundedBelow` holds for every colour set.
-/

noncomputable section

namespace OddMath.KrullSchmidtNil

open CategoryTheory

/-- Pulling back an inclusion `A ≤ P ⊔ span E` along a linear equivalence. -/
theorem comap_le_sup_span_of_equiv {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) {A P : Submodule k W} {E : Set W}
    (h : A ≤ P ⊔ Submodule.span k E) :
    A.comap e.toLinearMap ≤ P.comap e.toLinearMap ⊔ Submodule.span k (e.symm '' E) := by
  intro x hx
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp (h hx)
  refine Submodule.mem_sup.mpr ⟨e.symm p, ?_, e.symm q, ?_, ?_⟩
  · simpa [Submodule.mem_comap] using hp
  · have : e.symm q ∈ (Submodule.span k E).map e.symm.toLinearMap :=
      Submodule.mem_map_of_mem hq
    rwa [Submodule.map_span] at this
  · apply e.injective
    simp [hpq]

/-- A degree piece that lies, modulo a submodule, in a finite-dimensional span has
finite-dimensional quotient by that submodule. -/
theorem finiteDimensional_quotient_of_le_sup_span {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] {A P : Submodule k V} {E : Set V} (hE : E.Finite)
    (h : A ≤ P ⊔ Submodule.span k E) :
    FiniteDimensional k (A ⧸ P.comap A.subtype) := by
  let u : A →ₗ[k] V ⧸ P := P.mkQ ∘ₗ A.subtype
  have : FiniteDimensional k (Submodule.span k E) := FiniteDimensional.span_of_finite k hE
  have hr : LinearMap.range u ≤ (Submodule.span k E).map P.mkQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp (h a.2)
    refine ⟨e, he, ?_⟩
    change P.mkQ e = P.mkQ a
    have hp0 : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hp
    rw [← hpe, map_add, hp0, zero_add]
  have : FiniteDimensional k (LinearMap.range u) :=
    Submodule.finiteDimensional_of_le hr
  have hker : LinearMap.ker u = P.comap A.subtype := by
    ext a
    simp only [u, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  exact LinearEquiv.finiteDimensional
    ((Submodule.quotEquivOfEq _ _ hker).symm.trans u.quotKerEquivRange).symm

end OddMath.KrullSchmidtNil

namespace OddMath.SKM

open CategoryTheory StringDiagrams StringDiagrams.Presentation GradedSupercategory

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [Field k] (sy : Symmetrizer D) (Sc : Scalars D k)

/-- The 2-morphisms `E_s 1_μ ⟶ E_t 1_μ` that factor as a homogeneous closed diagram of
degree at least `d` in the rightmost region followed by a homogeneous 2-morphism. -/
def bubbleGen (μ : X) (s t : List (Letter I)) (d : ℕ) :
    Set ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
  {f | ∃ (z w : ℤ × ZMod 2) (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []))
      (h : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)),
      β ∈ wordHomComponent sy Sc μ [] [] z ∧ (d : ℤ) ≤ z.1 ∧
      h ∈ wordHomComponent sy Sc μ s t w ∧ f = bubAt D Sc μ s β ≫ h}

/-- The bubble filtration: the span of `bubbleGen`. -/
def bubbleFilt (μ : X) (s t : List (Letter I)) (d : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :=
  Submodule.span k (bubbleGen sy Sc μ s t d)

variable {sy Sc} in
theorem bubbleGen_mono {μ : X} {s t : List (Letter I)} {d e : ℕ} (hde : d ≤ e) :
    bubbleGen sy Sc μ s t e ⊆ bubbleGen sy Sc μ s t d := by
  rintro f ⟨z, w, β, h, hβ, hz, hh, rfl⟩
  exact ⟨z, w, β, h, hβ, le_trans (by exact_mod_cast hde) hz, hh, rfl⟩

theorem bubbleFilt_antitone {μ : X} {s t : List (Letter I)} {d e : ℕ} (hde : d ≤ e) :
    bubbleFilt sy Sc μ s t e ≤ bubbleFilt sy Sc μ s t d :=
  Submodule.span_mono (bubbleGen_mono hde)

/-- Bubble slides make the generators of the bubble filtration multiplicative. -/
theorem bubbleGen_comp {μ : X} {s t r : List (Letter I)} {a b : ℕ}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    {g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)}
    (hf : f ∈ bubbleGen sy Sc μ s t a) (hg : g ∈ bubbleGen sy Sc μ t r b) :
    f ≫ g ∈ bubbleFilt sy Sc μ s r (a + b) := by
  obtain ⟨z, w, β, h, hβ, hz, hh, rfl⟩ := hf
  obtain ⟨z', w', γ, h', hγ, hz', hh', rfl⟩ := hg
  have hslide : h ≫ bubAt D Sc μ t γ = zsign k (w.2 * z'.2) • (bubAt D Sc μ s γ ≫ h) :=
    comp_bubAt hh.2 hγ.2
  have heq : (bubAt D Sc μ s β ≫ h) ≫ (bubAt D Sc μ t γ ≫ h') =
      zsign k (w.2 * z'.2) • (bubAt D Sc μ s (β ≫ γ) ≫ (h ≫ h')) := by
    rw [Category.assoc, ← Category.assoc h, hslide, Linear.smul_comp, Linear.comp_smul,
      bubAt_comp, Category.assoc, Category.assoc]
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨z + z', w + w', β ≫ γ, h ≫ h',
    ⟨comp_mem_homDeg hβ.1 hγ.1, comp_mem_homPar hβ.2 hγ.2⟩, ?_,
    ⟨comp_mem_homDeg hh.1 hh'.1, comp_mem_homPar hh.2 hh'.2⟩, rfl⟩)
  change ((a + b : ℕ) : ℤ) ≤ z.1 + z'.1
  push_cast
  omega

/-- The bubble filtration is multiplicative. -/
theorem bubbleFilt_comp {μ : X} {s t r : List (Letter I)} {a b : ℕ}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    {g : (pres D Sc).obj (ob D μ t) ⟶ (pres D Sc).obj (ob D μ r)}
    (hf : f ∈ bubbleFilt sy Sc μ s t a) (hg : g ∈ bubbleFilt sy Sc μ t r b) :
    f ≫ g ∈ bubbleFilt sy Sc μ s r (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | mem g hg => exact bubbleGen_comp sy Sc hf hg
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add g₁ g₂ _ _ h₁ h₂ => rw [Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c g _ h => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c h
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => rw [Preadditive.add_comp]; exact Submodule.add_mem _ h₁ h₂
  | smul c f _ h => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c h

section Spanning

variable {sy Sc} (cs : CScalars Sc)

/-- Each member of the spanning set of Theorem 8.1 is a generator of the bubble filtration,
at the degree of its coefficient word. -/
theorem wordEval_mem_bubbleGen (μ : X) {s t : List (Letter I)} (F : MatchingBasisChoice s t)
    (u : F.Labels × List (SYMGen D)) :
    F.wordEval cs μ u ∈
      bubbleGen sy Sc μ s t ((u.2.map (symGenDegree D sy)).sum).toNat := by
  have hn : 0 ≤ (u.2.map (symGenDegree D sy)).sum :=
    List.sum_nonneg (fun x hx => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      exact (symGenDegree_pos sy g).le)
  refine ⟨SYM.wordBidegree sy u.2,
    (tableDegree D sy μ (F.layers u.1), xpar D μ (F.layers u.1)),
    betaSYM cs μ ((u.2.map (SYM.ι D k)).prod), xev cs μ s t (F.layers u.1), ?_, ?_,
    ⟨xev_mem_gdeg sy cs μ s t _, xev_mem_homPar cs μ s t _⟩, rfl⟩
  · exact beta_component_mem sy cs μ _ (Submodule.subset_span ⟨u.2, rfl, rfl⟩)
  · change (((u.2.map (symGenDegree D sy)).sum).toNat : ℤ) ≤ (u.2.map (symGenDegree D sy)).sum
    omega

include cs

/-- The bubble filtration starts with the whole Hom-space. -/
theorem bubbleFilt_zero (μ : X) (s t : List (Letter I)) :
    bubbleFilt sy Sc μ s t 0 = ⊤ := by
  obtain ⟨F⟩ := MatchingBasisChoice.nonempty s t
  apply top_unique
  rw [← F.span_wordEval cs μ]
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  exact Submodule.subset_span
    (bubbleGen_mono (Nat.zero_le _) (wordEval_mem_bubbleGen cs μ F u))

variable (sy) in
/-- **Uniform lower degree bound for every colour set.** The integer-degree pieces of a
Hom-space of `𝔘(𝔤)` vanish below a bound, by the lower bound on the degrees of the spanning set
of Theorem 8.1. No finiteness of the colour set is needed. -/
theorem hom_boundedBelow (hc : Sc.Homogeneous) (μ : X) (a b : List (Letter I)) :
    ∃ N, ∀ n < N, (pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) n = ⊥ := by
  obtain ⟨F⟩ := MatchingBasisChoice.nonempty a b
  obtain ⟨N, hN⟩ := F.wordDegree_bounded_below sy μ
  exact ⟨N, fun n hn => GradedSpanning.component_eq_bot _
    (isInternal_homDeg_gdeg D sy Sc hc _ _) (F.wordEval cs μ) (F.wordDegree sy μ)
    (F.wordEval_mem_gdeg sy cs μ) (F.span_wordEval cs μ) N hN hn⟩

/-- In each fixed degree, the bubble filtration vanishes in high index. -/
theorem bubbleFilt_vanish (hc : Sc.Homogeneous) (μ : X) (s t : List (Letter I)) (n : ℤ) :
    ∃ m : ℕ, ∀ x ∈ bubbleFilt sy Sc μ s t m,
      x ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ s) (ob D μ t) n → x = 0 := by
  obtain ⟨N, hN⟩ := hom_boundedBelow sy cs hc μ s t
  refine ⟨(n - N + 1).toNat, fun x hx hxn => ?_⟩
  let π := homogeneousComponent (a := ob D μ s) (b := ob D μ t)
    (isHomogeneous_gdeg D sy Sc hc) n
  rw [← homogeneousComponent_of_mem (isHomogeneous_gdeg D sy Sc hc) hxn]
  change π x = 0
  clear hxn
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, w, β, h, hβ, hz, hh, rfl⟩ := hy
    by_cases hw : w.1 < N
    · have h0 : h = 0 := by
        have := hh.1
        rw [hN _ hw] at this
        exact (Submodule.mem_bot k).mp this
      rw [h0, Limits.comp_zero, map_zero]
    · exact homogeneousComponent_of_mem_of_ne _
        (comp_mem_homDeg (bubAt_mem_gdeg sy s hβ.1) hh.1) (by omega)
  | zero => exact map_zero π
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- Modulo the first step of the bubble filtration, each degree piece lies in the span of
the finitely many decorated diagrams of that degree with no bubbles. -/
theorem homDeg_le_bubbleFilt_sup (hc : Sc.Homogeneous) (μ : X) (s t : List (Letter I))
    (n : ℤ) : ∃ E : Set ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)),
      E.Finite ∧ (pres D Sc).homDeg (gdeg D sy) (ob D μ s) (ob D μ t) n ≤
        bubbleFilt sy Sc μ s t 1 ⊔ Submodule.span k E := by
  obtain ⟨F⟩ := MatchingBasisChoice.nonempty s t
  refine ⟨(fun l => F.wordEval cs μ (l, [])) ''
      {l | tableDegree D sy μ (F.layers l) = n}, (F.degree_finite sy μ n).image _, ?_⟩
  rw [GradedSpanning.component_eq_span _ (isInternal_homDeg_gdeg D sy Sc hc _ _)
    (F.wordEval cs μ) (F.wordDegree sy μ) (F.wordEval_mem_gdeg sy cs μ)
    (F.span_wordEval cs μ) n]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨l, c⟩, hu, rfl⟩
  cases c with
  | nil =>
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨l, ?_, rfl⟩)
    change tableDegree D sy μ (F.layers l) + _ = n at hu
    simpa using hu
  | cons g c =>
    refine Submodule.mem_sup_left (Submodule.subset_span (bubbleGen_mono ?_
      (wordEval_mem_bubbleGen cs μ F (l, g :: c))))
    have hg := symGenDegree_pos sy g
    have hn : 0 ≤ (c.map (symGenDegree D sy)).sum :=
      List.sum_nonneg (fun x hx => by
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
        exact (symGenDegree_pos sy g).le)
    simp only [List.map_cons, List.sum_cons]
    omega

end Spanning

/-! ## The bubble filtration on the completed hom categories -/

variable {sy Sc}

/-- Transport of 2-morphisms along equalities of objects of the free 2-category. -/
def homCast {A A' B B' : Obj (sig D)} (hA : A = A') (hB : B = B') :
    ((pres D Sc).obj A ⟶ (pres D Sc).obj B) ≃ₗ[k] ((pres D Sc).obj A' ⟶ (pres D Sc).obj B') := by
  subst hA hB; exact LinearEquiv.refl k _

theorem homCast_comp {A A' B B' C C' : Obj (sig D)} (hA : A = A') (hB : B = B') (hC : C = C')
    (x : (pres D Sc).obj A ⟶ (pres D Sc).obj B) (y : (pres D Sc).obj B ⟶ (pres D Sc).obj C) :
    homCast (Sc := Sc) hA hC (x ≫ y) = homCast hA hB x ≫ homCast hB hC y := by
  subst hA hB hC; rfl

theorem homCast_mem_homDeg_iff {A A' B B' : Obj (sig D)} (hA : A = A') (hB : B = B')
    (x : (pres D Sc).obj A ⟶ (pres D Sc).obj B) (n : ℤ) :
    homCast hA hB x ∈ (pres D Sc).homDeg (gdeg D sy) A' B' n ↔
      x ∈ (pres D Sc).homDeg (gdeg D sy) A B n := by
  subst hA hB; exact Iff.rfl

variable (sy) {hc : Sc.Homogeneous}

variable (hc) in
/-- Well-formed categorical words have the standard presentation at their target weight. -/
theorem UGr.homObj_normal {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    f.obj = ob D b.region (f.obj.word.map Col.l) := by
  obtain ⟨hw, hs⟩ := word_eq_wd (D := D) f.obj.start f.obj.word f.wf
  change f.obj.word = wd D f.obj.endR _ at hw
  change f.obj.start = wt D f.obj.endR _ at hs
  rw [f.endR_eq] at hw hs
  exact Obj.ext hs hw

/-- The underlying word of a 1-morphism, as a list of letters. -/
abbrev UGr.letters {a b : UGr D Sc sy hc} (f : a ⟶ b) : List (Letter I) :=
  f.obj.word.map Col.l

/-- The bubble filtration on the hom category `a ⟶ b` of `𝔘(𝔤)`. -/
def UGr.bubbleFilt {a b : UGr D Sc sy hc} (d : ℕ) (f g : a ⟶ b) :
    Submodule k (f ⟶ g) :=
  (OddMath.SKM.bubbleFilt sy Sc b.region (UGr.letters sy f) (UGr.letters sy g) d).comap
    (homCast (UGr.homObj_normal sy hc f) (UGr.homObj_normal sy hc g)).toLinearMap

/-- **The bubble filtration is a graded nilpotent filtration** of each hom category of
`𝔘(𝔤)`, for every colour set (BE2 §11, the Krull–Schmidt input of Theorem 11.7). -/
def UGr.nilFiltration (cs : CScalars Sc) (a b : UGr D Sc sy hc) :
    KrullSchmidtNil.GradedNilFiltration k (C := a ⟶ b) where
  G d f g := UGr.bubbleFilt sy d f g
  zero f g := by
    apply top_unique
    intro x _
    change _ ∈ OddMath.SKM.bubbleFilt sy Sc _ _ _ 0
    rw [bubbleFilt_zero cs]
    trivial
  antitone d f g x hx := bubbleFilt_antitone sy Sc (Nat.le_succ d) hx
  comp_mem {_ _ f g h x y} hx hy := by
    change homCast (UGr.homObj_normal sy hc f) (UGr.homObj_normal sy hc h) (x ≫ y) ∈
      OddMath.SKM.bubbleFilt sy Sc _ _ _ _
    rw [homCast_comp (UGr.homObj_normal sy hc f) (UGr.homObj_normal sy hc g)
      (UGr.homObj_normal sy hc h)]
    exact bubbleFilt_comp sy Sc hx hy
  vanish f g n := by
    obtain ⟨m, hm⟩ := bubbleFilt_vanish cs hc b.region (UGr.letters sy f) (UGr.letters sy g) n
    refine ⟨m, fun x hx hxn => ?_⟩
    have hxn' : x ∈ (pres D Sc).homDeg (gdeg D sy) f.obj g.obj n := hxn
    have := hm _ hx ((homCast_mem_homDeg_iff _ _ x n).mpr hxn')
    exact (homCast (UGr.homObj_normal sy hc f) (UGr.homObj_normal sy hc g)).map_eq_zero_iff.mp
      this
  finiteDimensional f g n := by
    obtain ⟨E, hE, hle⟩ := homDeg_le_bubbleFilt_sup (sy := sy) cs hc b.region
      (UGr.letters sy f) (UGr.letters sy g) n
    let e := homCast (Sc := Sc) (UGr.homObj_normal sy hc f) (UGr.homObj_normal sy hc g)
    refine KrullSchmidtNil.finiteDimensional_quotient_of_le_sup_span (hE.image e.symm)
      (le_trans (fun x hx => (homCast_mem_homDeg_iff (sy := sy) (UGr.homObj_normal sy hc f)
        (UGr.homObj_normal sy hc g) x n).mpr hx)
        (KrullSchmidtNil.comap_le_sup_span_of_equiv e hle))

end OddMath.SKM
