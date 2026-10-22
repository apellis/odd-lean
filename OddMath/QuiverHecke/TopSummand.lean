/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.TopIdempotent
import OddMath.QuiverHecke.SortedSummands
import OddMath.QuiverHecke.LocalSummands

/-!
# The top idempotent in the completed 2-category

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. Transfer `top_localMod` from the endomorphisms of `E_s F_t 1_{-ν}` to the shifted word
`W = Q^m Π^a E_s F_t 1_{-ν}` in `𝔘̇(𝔤)`:

* `topIdeal`: the endomorphisms of `W` factoring through shorter words, a two-sided ideal
  (`topIdeal_isIdeal`);
* `top_localModT`: the top idempotent `α′(z′) α(z)` of `W` is local modulo `topIdeal`;
* `top_low`: an indecomposable retract `Q` of `W` whose idempotent lies in `topIdeal` is a
  retract of a shifted word `Q^n Π^b E_u 1_{-ν}` with `|u| + 2 ≤ |s| + |t|` (`LowWidth`);
* `top_sub_mem_closure_low`: if an indecomposable `Z` which is not low is a retract of the image
  `E` of the top idempotent, then `[E] - [Z]` is a sum of classes of low indecomposables.

Auxiliary: `proj0_mem_span_thru` (the degree-zero part of the maps through shorter words is
spanned by composites of normal-form diagrams of opposite degrees and equal parities) and
`exists_retract_thru` (a retract through such composites is a retract of a shorter word),
`exists_retract_of_mem_span`, and `localModT_of_sval` (local modulo shorter words, checked on the
underlying endomorphisms).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation GradedWalk K0Relations
open StringDiagrams.KrullSchmidt
open QuiverHecke (upWord hObj homPiece heCorner IsIdealEnd LocalModT compPow)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [Field k]
  {Sc : Scalars D k} (cs : CScalars Sc) (sy : Symmetrizer D) (hc : Sc.Homogeneous)

/-! ## Degree-zero composites through shorter words -/

section Thru

variable {sy}

theorem cl_mem_parity {μ : X} {s t : List (Letter I)} {L : List (LayerData I)}
    (hL : SChain s L t) :
    cl D Sc μ s t L ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ (parL (D := D) L) := by
  rw [cl_of hL]
  exact diag_mem_homDeg' (degree_parity_mkD D μ L hL)

variable {hc}

theorem proj0_cl_comp_mem {μ : X} {a u : List (Letter I)} {P : List (Letter I) → Prop}
    (hu : P u) {A B : List (LayerData I)} (hA : SChain a A u) (hB : SChain u B a) :
    proj0 sy hc μ a a (cl D Sc μ a u A ≫ cl D Sc μ u a B) ∈
      Submodule.span k (thruSet (Sc := Sc) sy μ a P) := by
  have g₁ := cl_mem_gdeg (Sc := Sc) sy μ a u A
  have g₂ := cl_mem_gdeg (Sc := Sc) sy μ u a B
  have p₁ := cl_mem_parity (Sc := Sc) (μ := μ) hA
  have p₂ := cl_mem_parity (Sc := Sc) (μ := μ) hB
  by_cases h0 : gsum D sy μ A + gsum D sy μ B = 0 ∧ parL (D := D) A + parL (D := D) B = 0
  · rw [proj0_of_mem (h0.1 ▸ comp_mem_homDeg g₁ g₂) (h0.2 ▸ comp_mem_homDeg p₁ p₂)]
    refine Submodule.subset_span ⟨u, A, B, hu, hA, hB, h0.1, ?_, rfl⟩
    rw [eq_neg_of_add_eq_zero_left h0.2, ZModModule.neg_eq_self]
  · rw [proj0_eq_zero (comp_mem_homDeg g₁ g₂) (comp_mem_homDeg p₁ p₂) (not_and_or.mp h0)]
    exact Submodule.zero_mem _

/-- **The degree-zero part of the maps through shorter words** is spanned by composites of
normal-form diagrams of opposite degrees and equal parities through shorter words. -/
theorem proj0_mem_span_thru {μ : X} {a : List (Letter I)}
    {x : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ a)}
    (hx : x ∈ ShortSpan Sc μ a a) :
    proj0 sy hc μ a a x ∈
      Submodule.span k (thruSet (Sc := Sc) sy μ a (fun u => u.length + 2 ≤ a.length)) := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, hu, g, h, rfl⟩ := hf
    have hg := mem_span_cl (Sc := Sc) μ g
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨A, hA, rfl⟩ := hg
      have hh := mem_span_cl (Sc := Sc) μ h
      induction hh using Submodule.span_induction with
      | mem h hh =>
        obtain ⟨B, hB, rfl⟩ := hh
        exact proj0_cl_comp_mem (P := fun u => u.length + 2 ≤ a.length) hu hA hB
      | zero => rw [Limits.comp_zero, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [Preadditive.comp_add, map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Linear.comp_smul, map_smul]; exact Submodule.smul_mem _ c hx
    | zero => rw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Linear.smul_comp, map_smul]; exact Submodule.smul_mem _ c hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

variable (hc) in
include hc in
theorem mem_span_thru_of_short {μ : X} {a : List (Letter I)}
    {x : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ a)}
    (hx : x ∈ ShortSpan Sc μ a a) (h₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ 0)
    (h₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ 0) :
    x ∈ Submodule.span k (thruSet (Sc := Sc) sy μ a (fun u => u.length + 2 ≤ a.length)) := by
  have := proj0_mem_span_thru (sy := sy) (hc := hc) hx
  rwa [proj0_of_mem h₁ h₂] at this

end Thru

/-! ## Retracts through composites of normal-form diagrams -/

section Retract

variable (hf : sy.DegreeLocallyFinite)

include cs hf in
/-- An indecomposable `Z` with `1_Z = ι t π`, where `t` is an endomorphism of
`Q^m Π^a E_w 1_ν` given by composites of normal-form diagrams through words `u` with `P u`, is a
retract of some `Q^n Π^b E_u 1_ν` with `P u`. -/
theorem exists_retract_thru {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} {P : List (Letter I) → Prop} {Z : weight Sc sy hc μ ⟶ weight Sc sy hc ν}
    (hZ : IsIndec Z) (t : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a)
    (ht : t.1.1 ∈ Submodule.span k (thruSet (Sc := Sc) sy ν w P))
    (ι : Z ⟶ completed Sc sy hc μ ν w hw m a) (π : completed Sc sy hc μ ν w hw m a ⟶ Z)
    (h : ι ≫ (inclusion Sc sy hc μ ν).map t ≫ π = 𝟙 Z) :
    ∃ (u : List (Letter I)) (hu : wt D ν u = μ) (n : ℤ) (b : ZMod 2), P u ∧
      ∃ (ι' : Z ⟶ completed Sc sy hc μ ν u hu n b)
        (π' : completed Sc sy hc μ ν u hu n b ⟶ Z), ι' ≫ π' = 𝟙 Z := by
  have : HomFinite k (weight Sc sy hc μ ⟶ weight Sc sy hc ν) := by
    let a : UGr D Sc sy hc := ⟨μ⟩
    let b : UGr D Sc sy hc := ⟨ν⟩
    have := UGr.degreeHomFinite sy cs hc hf a b
    exact inferInstanceAs (HomFinite k (GSKar k (a ⟶ b)))
  obtain ⟨N, c, g, hg⟩ := Submodule.mem_span_set'.mp ht
  choose u A B hP hA hB hd hp hfg using fun j => (g j).2
  have hu : ∀ j, wt D ν (u j) = μ := fun j => ((hA j).wt_eq D ν).trans hw
  let n : Fin N → ℤ := fun j => m - gsum D sy ν (A j)
  let b : Fin N → ZMod 2 := fun j => a + parL (D := D) (A j)
  let U : ∀ j, shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν (u j) (hu j) (n j) (b j) :=
    fun j => c j • lift Sc sy hc (A j) (hA j) (by simp only [n]; ring)
      (by simp only [b]; rw [parity_add_self])
  let V : ∀ j, shifted Sc sy hc μ ν (u j) (hu j) (n j) (b j) ⟶ shifted Sc sy hc μ ν w hw m a :=
    fun j => lift Sc sy hc (B j) (hB j) (by simp only [n]; linarith [hd j])
      (by simp only [b]; rw [add_comm, ← add_assoc, ZModModule.add_self, zero_add, hp j])
  have htot : ∑ j, U j ≫ V j = t := by
    let forget : (shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) →+
        ((pres D Sc).obj (ob D ν w) ⟶ (pres D Sc).obj (ob D ν w)) :=
      { toFun := fun f => f.1.1
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hfi : Function.Injective forget := fun _ _ h => Subtype.ext (Subtype.ext h)
    apply hfi
    rw [map_sum]
    change ∑ j, (U j ≫ V j).1.1 = t.1.1
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfg j]
    simp only [U, V, Linear.smul_comp]
    rfl
  let F := inclusion Sc sy hc μ ν
  obtain ⟨j, -, π', hπ'⟩ := Summands.exists_retract_of_sum k hZ Finset.univ
    (fun j => ι ≫ F.map (U j)) (fun j => F.map (V j) ≫ π) (by
      calc ∑ j ∈ Finset.univ, (ι ≫ F.map (U j)) ≫ F.map (V j) ≫ π
          = ι ≫ F.map (∑ j, U j ≫ V j) ≫ π := by
            rw [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
            simp only [F.map_comp, Category.assoc]
        _ = 𝟙 Z := by rw [htot, h])
  exact ⟨u j, hu j, n j, b j, hP j, _, π', hπ'⟩

end Retract

/-! ## The top idempotent of a shifted sorted word -/

section Top

variable {sy hc}

/-- The underlying endomorphism of `E_w 1_ν`. -/
abbrev sval {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (f : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) :
    End ((pres D Sc).obj (ob D ν w)) :=
  f.1.1

/-- An endomorphism of degree zero and parity zero, as an endomorphism of a shifted word. -/
def shiftedEnd {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (x : (pres D Sc).obj (ob D ν w) ⟶ (pres D Sc).obj (ob D ν w))
    (h₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ 0)
    (h₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ 0) :
    shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a :=
  ⟨⟨x, by
    change x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (0 + (m - m))
    rw [sub_self, add_zero]
    exact h₁⟩, by
    change x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ (0 + (a + a))
    rw [ZModModule.add_self, add_zero]
    exact h₂⟩

theorem sval_shiftedEnd {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} (x : (pres D Sc).obj (ob D ν w) ⟶ (pres D Sc).obj (ob D ν w))
    (h₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ 0)
    (h₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ 0) :
    sval (shiftedEnd (hc := hc) (hw := hw) (m := m) (a := a) x h₁ h₂) = x :=
  rfl

theorem shifted_ext {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    {f g : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a}
    (h : f.1.1 = g.1.1) : f = g :=
  Subtype.ext (Subtype.ext h)

/-- An endomorphism of a shifted word has degree zero and parity zero. -/
theorem sval_mem {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (f : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) :
    sval f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D ν w) (ob D ν w) 0 ∧
      sval f ∈ (pres D Sc).homDeg (parityDeg (sig D)) (ob D ν w) (ob D ν w) 0 := by
  have h₁ : sval f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D ν w) (ob D ν w) (0 + (m - m)) :=
    f.1.2
  have h₂ : sval f ∈ (pres D Sc).homDeg (parityDeg (sig D)) (ob D ν w) (ob D ν w)
      (0 + (a + a)) := f.2
  rw [sub_self, add_zero] at h₁
  rw [ZModModule.add_self, add_zero] at h₂
  exact ⟨h₁, h₂⟩

theorem sval_comp {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (f g : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) :
    sval (f ≫ g) = sval g * sval f :=
  rfl

theorem sval_sub {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (f g : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) :
    sval (f - g) = sval f - sval g :=
  rfl

theorem sval_compPow {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (f : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a) (n : ℕ) :
    sval (compPow f n) = sval f ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sval (compPow f n ≫ f) = _
    rw [sval_comp, ih, pow_succ']

theorem map_compPow {C E : Type*} [Category C] [Category E] (F : C ⥤ E) {W : C} (f : W ⟶ W)
    (n : ℕ) : F.map (compPow f n) = compPow (F.map f) n := by
  induction n with
  | zero => exact F.map_id W
  | succ n ih => change F.map (compPow f n ≫ f) = compPow (F.map f) n ≫ F.map f; rw [F.map_comp, ih]

variable (sy hc) in
/-- The endomorphisms of `Q^m Π^a E_w 1_ν` in `𝔘̇(𝔤)` factoring through shorter words. -/
def topIdeal (μ ν : X) (w : List (Letter I)) (hw : wt D ν w = μ) (m : ℤ) (a : ZMod 2) :
    Submodule k (completed Sc sy hc μ ν w hw m a ⟶ completed Sc sy hc μ ν w hw m a) :=
  Submodule.span k ((inclusion Sc sy hc μ ν).map ''
    {ψ | sval ψ ∈ ShortSpan Sc ν w w})

theorem map_mem_topIdeal {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} (φ : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a)
    (h : sval φ ∈ ShortSpan Sc ν w w) :
    (inclusion Sc sy hc μ ν).map φ ∈ topIdeal sy hc μ ν w hw m a :=
  Submodule.subset_span ⟨φ, h, rfl⟩

theorem map_comp_sub_mem_topIdeal {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} (φ ψ ε : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a)
    (h : sval (φ ≫ ψ - ε) ∈ ShortSpan Sc ν w w) :
    (inclusion Sc sy hc μ ν).map φ ≫ (inclusion Sc sy hc μ ν).map ψ -
      (inclusion Sc sy hc μ ν).map ε ∈ topIdeal sy hc μ ν w hw m a := by
  rw [← Functor.map_comp, ← Functor.map_sub]
  exact map_mem_topIdeal _ h

/-- **The maps through shorter words form a two-sided ideal.** -/
theorem topIdeal_isIdeal (μ ν : X) (w : List (Letter I)) (hw : wt D ν w = μ) (m : ℤ)
    (a : ZMod 2) : IsIdealEnd (topIdeal sy hc μ ν w hw m a) := by
  set F := inclusion Sc sy hc μ ν
  constructor
  · intro x t ht
    obtain ⟨x₀, rfl⟩ := F.map_surjective x
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨ψ, hψ, rfl⟩ := ht
      rw [← F.map_comp]
      exact Submodule.subset_span ⟨_, shortSpan_mul_right Sc ν w (sval x₀) hψ, rfl⟩
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  · intro t x ht
    obtain ⟨x₀, rfl⟩ := F.map_surjective x
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨ψ, hψ, rfl⟩ := ht
      rw [← F.map_comp]
      exact Submodule.subset_span ⟨_, shortSpan_mul_left Sc ν w (sval x₀) hψ, rfl⟩
    | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

theorem inv_of_sval {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} (ε₀ ψ : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a)
    (x : End ((pres D Sc).obj (ob D ν w)))
    (hx₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) (ob D ν w) (ob D ν w) 0)
    (hx₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) (ob D ν w) (ob D ν w) 0)
    (hεx : sval ε₀ * x * sval ε₀ = x) (hx₃ : sval ψ * x - sval ε₀ ∈ ShortSpan Sc ν w w)
    (hx₄ : x * sval ψ - sval ε₀ ∈ ShortSpan Sc ν w w) :
    ∃ z, (inclusion Sc sy hc μ ν).map ε₀ ≫ z ≫ (inclusion Sc sy hc μ ν).map ε₀ = z ∧
      (inclusion Sc sy hc μ ν).map ψ ≫ z - (inclusion Sc sy hc μ ν).map ε₀ ∈
        topIdeal sy hc μ ν w hw m a ∧
      z ≫ (inclusion Sc sy hc μ ν).map ψ - (inclusion Sc sy hc μ ν).map ε₀ ∈
        topIdeal sy hc μ ν w hw m a := by
  obtain ⟨ω, hω⟩ : ∃ ω : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a,
      sval ω = x := ⟨_, sval_shiftedEnd (hc := hc) (hw := hw) (m := m) (a := a) x hx₁ hx₂⟩
  refine ⟨(inclusion Sc sy hc μ ν).map ω, ?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine shifted_ext ?_
    show sval (ε₀ ≫ ω ≫ ε₀) = sval ω
    rw [sval_comp, sval_comp, hω]
    exact hεx
  · rw [← Functor.map_comp, ← Functor.map_sub]
    refine Submodule.subset_span ⟨ψ ≫ ω - ε₀, ?_, rfl⟩
    show sval (ψ ≫ ω - ε₀) ∈ ShortSpan Sc ν w w
    rw [sval_sub, sval_comp, hω]
    exact hx₄
  · have h₃ : sval (ω ≫ ψ - ε₀) ∈ ShortSpan Sc ν w w := by
      rw [sval_sub, sval_comp, hω]
      exact hx₃
    exact map_comp_sub_mem_topIdeal ω ψ ε₀ h₃

/-- **Local modulo shorter words, from the underlying endomorphisms.** If every endomorphism `f`
of `E_w 1_ν` of degree zero and parity zero with `ε f ε = f` is nilpotent modulo the maps through
shorter words or invertible modulo them in `ε End ε` by an endomorphism of degree zero and parity
zero, then `ε` is local modulo `topIdeal` in `𝔘̇(𝔤)`. -/
theorem localModT_of_sval {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ}
    {a : ZMod 2} (ε₀ : shifted Sc sy hc μ ν w hw m a ⟶ shifted Sc sy hc μ ν w hw m a)
    (hloc : ∀ f : End ((pres D Sc).obj (ob D ν w)),
      f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D ν w) (ob D ν w) 0 →
      f ∈ (pres D Sc).homDeg (parityDeg (sig D)) (ob D ν w) (ob D ν w) 0 →
      sval ε₀ * f * sval ε₀ = f →
      (∃ N, f ^ (N + 1) ∈ ShortSpan Sc ν w w) ∨
        ∃ x : End ((pres D Sc).obj (ob D ν w)),
          x ∈ (pres D Sc).homDeg (gdeg D sy) (ob D ν w) (ob D ν w) 0 ∧
          x ∈ (pres D Sc).homDeg (parityDeg (sig D)) (ob D ν w) (ob D ν w) 0 ∧
          sval ε₀ * x * sval ε₀ = x ∧ f * x - sval ε₀ ∈ ShortSpan Sc ν w w ∧
          x * f - sval ε₀ ∈ ShortSpan Sc ν w w) :
    LocalModT (topIdeal sy hc μ ν w hw m a) ((inclusion Sc sy hc μ ν).map ε₀) := by
  intro y hy
  obtain ⟨ψ, rfl⟩ := (inclusion Sc sy hc μ ν).map_surjective y
  have hψ : ε₀ ≫ ψ ≫ ε₀ = ψ := (inclusion Sc sy hc μ ν).map_injective (by
    rw [(inclusion Sc sy hc μ ν).map_comp, (inclusion Sc sy hc μ ν).map_comp]
    exact hy)
  have hεf : sval ε₀ * sval ψ * sval ε₀ = sval ψ := by
    rw [← sval_comp, ← sval_comp, hψ]
  rcases hloc (sval ψ) (sval_mem ψ).1 (sval_mem ψ).2 hεf with ⟨N, hN⟩ |
    ⟨x, hx₁, hx₂, hεx, hx₃, hx₄⟩
  · refine Or.inl ⟨N, ?_⟩
    rw [← map_compPow]
    refine Submodule.subset_span ⟨compPow ψ (N + 1), ?_, rfl⟩
    show sval (compPow ψ (N + 1)) ∈ ShortSpan Sc ν w w
    rw [sval_compPow]
    exact hN
  · exact Or.inr (inv_of_sval ε₀ ψ x hx₁ hx₂ hεx hx₃ hx₄)

include cs in
/-- **The top idempotent is local modulo shorter words in `𝔘̇(𝔤)`** (BE2, arXiv:1701.04133v2,
proof of Theorem 11.7). Let `z`, `z′` be even degree-zero idempotents of `E_s`, `E_t` with local
corners. The idempotent `α′(z′) α(z)` of `Q^m Π^a E_s F_t 1_{-ν}` is local modulo the maps
through shorter words. -/
theorem top_localModT {μ ν : X} {s t : List I} {hw : wt D (-ν) (upWord s ++ dnWord t) = μ}
    {m : ℤ} {a : ZMod 2} {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz : z ≫ z = z) (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) {NE NE' : Submodule k _} {b b' lo lo' : ℕ}
    (hE : LocalCorner (heCorner z) z NE b lo) (hE' : LocalCorner (heCorner z') z' NE' b' lo')
    (ε₀ : shifted Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a ⟶
      shifted Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a)
    (hε₀ : sval ε₀ = topEps sy hc ν s t z z') :
    LocalModT (topIdeal sy hc μ (-ν) _ hw m a) ((inclusion Sc sy hc μ (-ν)).map ε₀) := by
  refine localModT_of_sval ε₀ fun f hf₁ hf₂ hεf => ?_
  rw [hε₀] at hεf ⊢
  rcases top_localMod cs hz hz' hz0 hz0' hE hE' ⟨hf₁, hf₂⟩ hεf with h | ⟨x, hx, h₁, h₂, h₃⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx.1, hx.2, h₁, h₂, h₃⟩

end Top

/-! ## Low summands -/

section Low

open QuiverHecke (IsRetract of_sub_mem_closure_low)

variable (hf : sy.DegreeLocallyFinite)

/-- An indecomposable retract `Q` of `W` whose idempotent lies in the span of `T` satisfies
`1_Q = ι t π` for some `t ∈ T`. -/
theorem exists_retract_of_mem_span {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] (k : Type*) [Field k]
    [Linear k 𝒞] [HomFinite k 𝒞] {Q W : 𝒞} (hQ : IsIndec Q) (fQ : Q ⟶ W) (gQ : W ⟶ Q)
    (hfg : fQ ≫ gQ = 𝟙 Q) {T : Set (W ⟶ W)} (hT : gQ ≫ fQ ∈ Submodule.span k T) :
    ∃ t ∈ T, ∃ (ι : Q ⟶ W) (π : W ⟶ Q), ι ≫ t ≫ π = 𝟙 Q := by
  have key : ∀ x ∈ Submodule.span k T,
      fQ ≫ x ≫ gQ ∈ Submodule.span k {r | ∃ t ∈ T, r = fQ ≫ t ≫ gQ} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [Limits.zero_comp, Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  have hspan := key _ hT
  rw [← Category.assoc, ← Category.assoc, hfg, Category.id_comp, hfg] at hspan
  obtain ⟨N, c, r, hr⟩ := Submodule.mem_span_set'.mp hspan
  choose t ht hr' using fun j => (r j).2
  obtain ⟨j, -, v', hv'⟩ := Summands.exists_retract_of_sum k hQ Finset.univ
    (fun j => c j • fQ ≫ t j) (fun _ => gQ) (by
      rw [← hr]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hr' j, Linear.smul_comp, Category.assoc])
  exact ⟨t j, ht j, c j • fQ, v', by rw [← Category.assoc, Linear.smul_comp]; exact hv'⟩

/-- The summands of shifted words `Q^n Π^b E_u 1_ν` with `|u| + 2 ≤ N`. -/
def LowWidth (μ ν : X) (N : ℕ) (Q : weight Sc sy hc μ ⟶ weight Sc sy hc ν) : Prop :=
  ∃ (u : List (Letter I)) (hu : wt D ν u = μ) (n : ℤ) (b : ZMod 2), u.length + 2 ≤ N ∧
    IsRetract Q (completed Sc sy hc μ ν u hu n b)

include cs hf in
/-- **Indecomposable retracts through shorter words are low**: an indecomposable retract `Q` of
`Q^m Π^a E_w 1_ν` whose idempotent factors through shorter words is a retract of a shifted word
with at least two letters fewer. -/
theorem top_low {μ ν : X} {w : List (Letter I)} {hw : wt D ν w = μ} {m : ℤ} {a : ZMod 2}
    (Q : weight Sc sy hc μ ⟶ weight Sc sy hc ν) (fQ : Q ⟶ completed Sc sy hc μ ν w hw m a)
    (gQ : completed Sc sy hc μ ν w hw m a ⟶ Q) (hfg : fQ ≫ gQ = 𝟙 Q)
    (hT : gQ ≫ fQ ∈ topIdeal sy hc μ ν w hw m a) (hQ : IsIndec Q) :
    LowWidth sy hc μ ν w.length Q := by
  have : HomFinite k (weight Sc sy hc μ ⟶ weight Sc sy hc ν) := by
    let a : UGr D Sc sy hc := ⟨μ⟩
    let b : UGr D Sc sy hc := ⟨ν⟩
    have := UGr.degreeHomFinite sy cs hc hf a b
    exact inferInstanceAs (HomFinite k (GSKar k (a ⟶ b)))
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, ι, π, h⟩ := exists_retract_of_mem_span k hQ fQ gQ hfg hT
  obtain ⟨u, hu, n, b, hP, ι', π', h'⟩ := exists_retract_thru cs sy hc hf hQ ψ
    (mem_span_thru_of_short hc hψ (sval_mem ψ).1 (sval_mem ψ).2) ι π h
  exact ⟨u, hu, n, b, hP, ι', π', h'⟩

include cs hf in
/-- **The top summand (BE2, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity).** Let
`z`, `z′` be even degree-zero idempotents of `E_s`, `E_t` with local corners, and `E` the image of
the top idempotent `α′(z′) α(z)` of `W = Q^m Π^a E_s F_t 1_{-ν}`. Call an object low if it is a
retract of a shifted word with at least two letters fewer than `W`. If an indecomposable `Z`
which is not low is a retract of `E`, then `[E] - [Z]` is a sum of classes of low
indecomposables. -/
theorem top_sub_mem_closure_low {μ ν : X} {s t : List I}
    {hw : wt D (-ν) (upWord s ++ dnWord t) = μ} {m : ℤ} {a : ZMod 2}
    {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz : z ≫ z = z) (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) {NE NE' : Submodule k _} {b b' lo lo' : ℕ}
    (hE : LocalCorner (heCorner z) z NE b lo) (hE' : LocalCorner (heCorner z') z' NE' b' lo')
    (ε₀ : shifted Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a ⟶
      shifted Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a)
    (hε₀ : sval ε₀ = topEps sy hc ν s t z z') {E : weight Sc sy hc μ ⟶ weight Sc sy hc (-ν)}
    (i : E ⟶ completed Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a)
    (p : completed Sc sy hc μ (-ν) (upWord s ++ dnWord t) hw m a ⟶ E) (hip : i ≫ p = 𝟙 E)
    (hpi : p ≫ i = (inclusion Sc sy hc μ (-ν)).map ε₀)
    {Z : weight Sc sy hc μ ⟶ weight Sc sy hc (-ν)}
    (hZ : IsIndec Z) (f : Z ⟶ E) (g : E ⟶ Z) (hfg : f ≫ g = 𝟙 Z)
    (hZlow : ¬ LowWidth sy hc μ (-ν) (upWord s ++ dnWord t).length Z) :
    K₀.mk E - K₀.mk Z ∈ AddSubmonoid.closure
      {x | ∃ Q, IsIndec Q ∧ LowWidth sy hc μ (-ν) (upWord s ++ dnWord t).length Q ∧
        x = K₀.mk Q} := by
  have : HomFinite k (weight Sc sy hc μ ⟶ weight Sc sy hc (-ν)) := by
    let a : UGr D Sc sy hc := ⟨μ⟩
    let b : UGr D Sc sy hc := ⟨-ν⟩
    have := UGr.degreeHomFinite sy cs hc hf a b
    exact inferInstanceAs (HomFinite k (GSKar k (a ⟶ b)))
  exact of_sub_mem_closure_low (topIdeal_isIdeal μ (-ν) _ hw m a) _
    (fun Q fQ gQ hfgQ hT hQ => top_low cs sy hc hf Q fQ gQ hfgQ hT hQ)
    (top_localModT cs hz hz' hz0 hz0' hE hE' ε₀ hε₀) i p hip hpi hZ f g hfg hZlow

end Low

end OddMath.SKM
