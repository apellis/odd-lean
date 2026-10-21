/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianHoms
import StringDiagrams.Super.PresentedGraded
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Homogeneous coefficient components for BE2 (dum)

The coefficient components are intrinsic subspaces of the abstract `SYM`:
spans of generator words with prescribed integer degree and parity. They do
not depend on a weight, a bubble evaluation, or the Nondegeneracy Conjecture.
These are the coefficient spaces in the graded restriction of the expansion
map used in the proof of Theorem 12.1 of arXiv:1701.04133v2.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- Parity of an abstract coefficient generator. Polynomial generators are even,
including those attached to odd colours. -/
def symGenParity : SYMGen D → ZMod 2
  | .inl _ => 0
  | .inr _ => 1

namespace SYM
variable (sy : Symmetrizer D) (k : Type w) [CommRing k]

/-- Evaluation of a word in the abstract coefficient generators. -/
def word (l : List (SYMGen D)) : SYM D k := (l.map (ι D k)).prod

/-- Integer degree and parity of a word in the coefficient generators. -/
def wordBidegree (l : List (SYMGen D)) : ℤ × ZMod 2 :=
  ((l.map (symGenDegree D sy)).sum, (l.map symGenParity).sum)

/-- Intrinsic homogeneous component of the presented coefficient algebra. -/
def component (z : ℤ × ZMod 2) : Submodule k (SYM D k) :=
  Submodule.span k (word k '' {l | wordBidegree sy l = z})

/-- Negative integer degrees contain no coefficient words. -/
theorem component_eq_bot (z : ℤ × ZMod 2) (hz : z.1 < 0) :
    component sy k z = ⊥ := by
  have he : {l | wordBidegree sy l = z} = (∅ : Set (List (SYMGen D))) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hn : 0 ≤ (l.map (symGenDegree D sy)).sum :=
      List.sum_nonneg (fun x hx => by
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
        exact (symGenDegree_pos sy g).le)
    have h := congrArg Prod.fst hl
    exact (not_le_of_gt hz) (h ▸ hn)
  simp only [component, he, Set.image_empty, Submodule.span_empty]

/-- The intrinsic coefficient components are finite-dimensional under the
explicit colour-degree local-finiteness condition. -/
theorem finiteDimensional_component {K : Type*} [Field K]
    (hf : sy.DegreeLocallyFinite) (z : ℤ × ZMod 2) :
    FiniteDimensional K (component sy K z) := by
  apply FiniteDimensional.span_of_finite
  apply Set.Finite.image
  apply (symGen_words_finite sy hf z.1).subset
  intro l hl
  exact le_of_eq (congrArg Prod.fst hl)

end SYM

variable {k : Type w} [CommRing k] {Sc : Scalars D k}
variable (sy : Symmetrizer D) (cs : CScalars Sc) (μ : X)

/-- The coefficient-generator evaluation preserves parity. -/
theorem betaSYMGen_mem_parity (g : SYMGen D) :
    betaSYMGen cs μ g ∈ closedPar D Sc μ (symGenParity g) := by
  cases g with
  | inl a => exact betaSYMGen_polynomial_mem cs μ a
  | inr i => simpa only [betaSYMGen, symGenParity, i.property] using oddBubble_mem cs i μ

/-- Every coefficient word evaluates in its declared parity. -/
theorem beta_word_mem_parity (l : List (SYMGen D)) :
    betaSYM cs μ (SYM.word k l) ∈ closedPar D Sc μ (SYM.wordBidegree sy l).2 := by
  induction l with
  | nil =>
      change betaSYM cs μ 1 ∈ closedPar D Sc μ 0
      rw [map_one]
      simpa only [cl_nil, parsum_nil, End.one_def] using
        (cl_mem_closedPar (D := D) (Sc := Sc) (μ := μ) (L := []) (by rfl) rfl)
  | cons g l ih =>
      simp only [SYM.word, SYM.wordBidegree, List.map_cons, List.prod_cons,
        List.sum_cons, map_mul, betaSYM_ι]
      simpa only [add_comm, End.mul_def, SYM.word, SYM.wordBidegree] using
        comp_mem_closedPar ih (betaSYMGen_mem_parity cs μ g)

/-- Homogeneous coefficient components map to the corresponding integer/parity
components of the endomorphisms of the empty word. -/
theorem beta_component_mem (z : ℤ × ZMod 2) {x : SYM D k}
    (hx : x ∈ SYM.component sy k z) :
    betaSYM cs μ x ∈
      (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) z.1 ⊓
        closedPar D Sc μ z.2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      subst z
      exact ⟨MatchingBasisChoice.beta_word_mem_gdeg sy cs μ l,
        beta_word_mem_parity sy cs μ l⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end OddMath.SKM
