/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.DimensionComponents

/-!
# Graded restriction of the BE2 expansion

Theorem 8.1 supplies spanning. The Nondegeneracy Conjecture supplies only
injectivity. Restriction to a fixed degree and parity is derived by homogeneous
projections; it is not added as an extra conjectural hypothesis.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The normal-form parity subspace lies in the presentation's parity grading. -/
theorem homPar_le_homDeg (μ : X) (a b : List (Letter I)) (p : ZMod 2) :
    homPar D Sc μ a b p ≤
      (pres D Sc).homDeg (parityDeg (sig D)) (ob D μ a) (ob D μ b) p := by
  apply Submodule.span_le.mpr
  rintro f ⟨L, hL, hp, rfl⟩
  rw [cl_of hL]
  exact lin_mem_homDeg (dg_mem D hp)

/-- The simultaneous integer/parity component of a word Hom. -/
def homComponent (sy : Symmetrizer D) (Sc : Scalars D k) (μ : X)
    (a b : List (Letter I)) (z : ℤ × ZMod 2) :
    Submodule k ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  (pres D Sc).homDeg (gdeg D sy) (ob D μ a) (ob D μ b) z.1 ⊓
    homPar D Sc μ a b z.2

/-- Project a spanning homogeneous family to one integer/parity component. -/
theorem homComponent_eq_span (sy : Symmetrizer D) (hc : Sc.Homogeneous)
    (μ : X) (a b : List (Letter I)) {α : Type*}
    (v : α → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (d : α → ℤ × ZMod 2) (hv : ∀ t, v t ∈ homComponent sy Sc μ a b (d t))
    (hs : Submodule.span k (Set.range v) = ⊤) (z : ℤ × ZMod 2) :
    homComponent sy Sc μ a b z = Submodule.span k (v '' {t | d t = z}) := by
  let pg := homogeneousComponent (a := ob D μ a) (b := ob D μ b)
    (isHomogeneous_gdeg D sy Sc hc) z.1
  let pp := homogeneousComponent (a := ob D μ a) (b := ob D μ b)
    (isParityHomogeneous D Sc) z.2
  let p := pp ∘ₗ pg
  have psame {x} (hx : x ∈ homComponent sy Sc μ a b z) : p x = x := by
    change pp (pg x) = x
    rw [show pg x = x from homogeneousComponent_of_mem _ hx.1]
    exact homogeneousComponent_of_mem _ (homPar_le_homDeg μ a b z.2 hx.2)
  have pne (t : α) (ht : d t ≠ z) : p (v t) = 0 := by
    change pp (pg (v t)) = 0
    by_cases hn : (d t).1 = z.1
    · rw [show pg (v t) = v t from homogeneousComponent_of_mem _ (hn ▸ (hv t).1)]
      apply homogeneousComponent_of_mem_of_ne _ (homPar_le_homDeg μ a b _ (hv t).2)
      exact fun hp => ht (Prod.ext hn hp)
    · rw [show pg (v t) = 0 from homogeneousComponent_of_mem_of_ne _ (hv t).1 hn,
        map_zero]
  apply le_antisymm
  · intro x hx
    have hxs : x ∈ Submodule.span k (Set.range v) := by rw [hs]; trivial
    rw [← psame hx]
    clear hx
    induction hxs using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨t, rfl⟩ := hx
        by_cases ht : d t = z
        · rw [psame (ht ▸ hv t)]
          exact Submodule.subset_span ⟨t, ht, rfl⟩
        · rw [pne t ht]; exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    exact ht ▸ hv t

/-- Rightmost placement preserves normal-form parity. -/
theorem bubAt_mem_parity {μ : X} (a : List (Letter I)) {p : ZMod 2}
    {x : End ((pres D Sc).obj (ob D μ []))} (hx : x ∈ closedPar D Sc μ p) :
    bubAt D Sc μ a x ∈ homPar D Sc μ a a p := by
  have hcast {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t')
      {y : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
      (hy : y ∈ homPar D Sc μ s t p) :
      wordCast μ hs ht y ∈ homPar D Sc μ s' t' p := by
    subst s' t'; exact hy
  exact hcast _ _ (plcL_mem μ a [] hx)

namespace MatchingBasisChoice
variable {a b : List (Letter I)} (F : MatchingBasisChoice a b)
variable (sy : Symmetrizer D) (cs : CScalars Sc) (μ : X)

/-- Bidegree of a decorated matching, with no coefficient attached. -/
def labelBidegree (t : F.Labels) : ℤ × ZMod 2 :=
  (tableDegree D sy μ (F.layers t), xpar D μ (F.layers t))

/-- Multiplication by a homogeneous abstract coefficient adds both degrees. -/
theorem coefficientMap_mem (t : F.Labels) (z : ℤ × ZMod 2) {x : SYM D k}
    (hx : x ∈ SYM.component sy k z) :
    F.coefficientMap cs μ t x ∈ homComponent sy Sc μ a b (F.labelBidegree sy μ t + z) := by
  obtain ⟨hg, hp⟩ := beta_component_mem sy cs μ z hx
  constructor
  · change F.coefficientMap cs μ t x ∈ (pres D Sc).homDeg (gdeg D sy)
      (ob D μ a) (ob D μ b) (F.labelBidegree sy μ t + z).1
    simpa only [coefficientMap, LinearMap.coe_mk, AddHom.coe_mk, labelBidegree,
      Prod.fst_add, add_comm] using comp_mem_homDeg (bubAt_mem_gdeg sy a hg)
        (xev_mem_gdeg sy cs μ a b (F.layers t))
  · change F.coefficientMap cs μ t x ∈ homPar D Sc μ a b (F.labelBidegree sy μ t + z).2
    simpa only [coefficientMap, LinearMap.coe_mk, AddHom.coe_mk, labelBidegree,
      Prod.snd_add, add_comm] using comp_mem_homPar (bubAt_mem_parity a hp)
        (xev_mem_homPar cs μ a b (F.layers t))

/-- Theorem 8.1's coefficient-word family is homogeneous in both gradings. -/
theorem wordEval_mem_component (t : F.Labels × List (SYMGen D)) :
    F.wordEval cs μ t ∈ homComponent sy Sc μ a b
      (F.labelBidegree sy μ t.1 + SYM.wordBidegree sy t.2) :=
  F.coefficientMap_mem sy cs μ t.1 _ (Submodule.subset_span ⟨t.2, rfl, rfl⟩)

/-- Finite coefficient expansions with the shifts prescribed by a fixed
integer/parity component. -/
def coefficientComponent (z : ℤ × ZMod 2) : Submodule k (F.Labels →₀ SYM D k) where
  carrier := {f | ∀ t, f t ∈ SYM.component sy k (z - F.labelBidegree sy μ t)}
  zero_mem' := fun _ => Submodule.zero_mem _
  add_mem' := fun hx hy t => Submodule.add_mem _ (hx t) (hy t)
  smul_mem' := fun r _ hx t => Submodule.smul_mem _ r (hx t)

/-- Restricting the expansion to shifted homogeneous coefficients preserves
the target component. -/
theorem expansion_mem_component (z : ℤ × ZMod 2)
    {f : F.Labels →₀ SYM D k} (hf : f ∈ F.coefficientComponent (k := k) sy μ z) :
    F.expansion cs μ f ∈ homComponent sy Sc μ a b z := by
  classical
  rw [expansion, Finsupp.lsum_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro t _
  simpa only [add_comm (F.labelBidegree sy μ t), sub_add_cancel] using
    F.coefficientMap_mem sy cs μ t (z - F.labelBidegree sy μ t) (hf t)

/-- The linear expansion map on a single homogeneous component. -/
def componentExpansion (z : ℤ × ZMod 2) :
    F.coefficientComponent (k := k) sy μ z →ₗ[k] homComponent sy Sc μ a b z :=
  (F.expansion cs μ ∘ₗ (F.coefficientComponent (k := k) sy μ z).subtype).codRestrict _
    (fun f => F.expansion_mem_component sy cs μ z f.property)

/-- Theorem 8.1 already gives surjectivity on every homogeneous component;
no independence hypothesis enters this assertion. -/
theorem componentExpansion_surjective (hc : Sc.Homogeneous) (z : ℤ × ZMod 2) :
    Function.Surjective (F.componentExpansion sy cs μ z) := by
  classical
  have hs := homComponent_eq_span sy hc μ a b (F.wordEval cs μ)
    (fun t => F.labelBidegree sy μ t.1 + SYM.wordBidegree sy t.2)
    (F.wordEval_mem_component sy cs μ) (F.span_wordEval cs μ) z
  have hsingle (t : F.Labels) (x : SYM D k)
      (hx : x ∈ SYM.component sy k (z - F.labelBidegree sy μ t)) :
      Finsupp.single t x ∈ F.coefficientComponent (k := k) sy μ z := by
    intro s
    by_cases h : t = s
    · subst s; simpa only [Finsupp.single_eq_same] using hx
    · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using
        (Submodule.zero_mem (SYM.component sy k (z - F.labelBidegree sy μ s)))
  let L := F.expansion cs μ ∘ₗ (F.coefficientComponent (k := k) sy μ z).subtype
  have hr : homComponent sy Sc μ a b z ≤ L.range := by
    rw [hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨t, l⟩, htl, rfl⟩
    have hl : SYM.wordBidegree sy l = z - F.labelBidegree sy μ t := by
      exact eq_sub_of_add_eq' htl
    refine ⟨⟨Finsupp.single t (SYM.word k l), hsingle t _ ?_⟩, ?_⟩
    · exact Submodule.subset_span ⟨l, hl, rfl⟩
    · exact F.expansion_single cs μ t (SYM.word k l)
  intro y
  obtain ⟨x, hx⟩ := hr y.property
  exact ⟨x, Subtype.ext hx⟩

/-- Under the selected-family form of the Nondegeneracy Conjecture, the
expansion identifies a homogeneous Hom component with its shifted coefficient
space. This is the graded restriction needed for BE2 Theorem 12.1, (dum). -/
def componentExpansionEquiv (hc : Sc.Homogeneous) (hF : F.IsBasis cs μ)
    (z : ℤ × ZMod 2) :
    F.coefficientComponent (k := k) sy μ z ≃ₗ[k] homComponent sy Sc μ a b z :=
  LinearEquiv.ofBijective (F.componentExpansion sy cs μ z)
    ⟨fun _ _ h => Subtype.ext (hF.1 (congrArg Subtype.val h)),
      F.componentExpansion_surjective sy cs μ hc z⟩

end MatchingBasisChoice
end OddMath.SKM
