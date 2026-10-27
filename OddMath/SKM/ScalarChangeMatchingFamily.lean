/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.ScalarChangeBubbleFamily
import OddMath.SKM.Nondegeneracy

/-!
# Specialization of the decorated matching expansion

Brundan–Ellis, *Super Kac–Moody 2-categories*, §8, Theorem 8.1 and
(1.21)–(1.22). The actual chosen decorated matchings and their full
polynomial/exterior bubble coefficients commute with coefficient change.
-/
noncomputable section
namespace OddMath.SKM.ScalarChange
open CategoryTheory StringDiagrams Presentation
open scoped TensorProduct
universe u v w w'
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)
  {Sc : Scalars D R} (cs : CScalars Sc)

/-- Horizontal placement respects coefficient change, including incompatible boundaries. -/
theorem homMap_plcL (μ : X) (u v s t : List (Letter I))
    (g : (pres D Sc).obj (ob D (wt D μ v) s) ⟶
      (pres D Sc).obj (ob D (wt D μ v) t)) :
    homMap f D Sc _ _ (plcL D Sc μ u v s t g) =
      plcL D (scalars D f Sc) μ u v s t (homMap f D Sc _ _ g) := by
  have hg := mem_span_cl (D := D) (Sc := Sc) (wt D μ v) g
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨L, hL, rfl⟩ := hg
      rw [plcL_cl, homMap_cl, homMap_cl, plcL_cl]
  | zero => simp
  | add x y _ _ hx hy =>
      simp only [map_add, hx, hy]
  | smul r x _ hx =>
      rw [map_smul, homMap_smul, hx, homMap_smul, map_smul]

/-- Placed rightmost bubbles retain their complete raw diagram, not only scalar coefficients. -/
theorem homMap_bubAt (μ : X) (v : List (Letter I))
    (g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])) :
    homMap f D Sc _ _ (bubAt D Sc μ v g) =
      bubAt D (scalars D f Sc) μ v (homMap f D Sc _ _ g) := by
  have hg := mem_span_cl (D := D) (Sc := Sc) μ g
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨L, hL, rfl⟩ := hg
      rw [bubAt_cl, homMap_cl, homMap_cl, bubAt_cl]
  | zero => simp
  | add x y _ _ hx hy =>
      simp only [map_add, hx, hy]
  | smul r x _ hx =>
      rw [map_smul, homMap_smul, hx, homMap_smul, map_smul]

/-- Every actual extended layer, including normalized left cups and caps,
commutes with specialization at the unchanged weight. -/
theorem homMap_xlay (μ : X) (x : XLayer I) :
    homMap f D Sc _ _ (xlay cs μ x) =
      xlay (cScalars D f cs) μ x := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g => exact homMap_cl f D Sc _ _ _ _
  | lcup i =>
      change homMap f D Sc _ _ (plcL D Sc μ a b [] [up i, dn i]
        (etaP cs i (wt D μ b))) = _
      rw [homMap_plcL, homMap_etaP]
      rfl
  | lcap i =>
      change homMap f D Sc _ _ (plcL D Sc μ a b [dn i, up i] []
        (epsP cs i (wt D μ b))) = _
      rw [homMap_plcL, homMap_epsP]
      rfl

/-- The actual extended diagram evaluator commutes with specialization,
including all bends, boundary casts and invalid chains. -/
theorem homMap_xev (μ : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    homMap f D Sc _ _ (xev cs μ s t L) =
      xev (cScalars D f cs) μ s t L := by
  induction L generalizing s with
  | nil => exact homMap_cl f D Sc _ _ _ _
  | cons x L ih =>
      rw [xev_cons, xev_cons, homMap_comp, homMap_comp,
        homMap_cl, homMap_xlay, ih]

/-- A fixed decorated matching and its full bubble coefficient specialize
without changing its representative, distinguished points, or dot serialization. -/
theorem homMap_expansion_single {a b : List (Letter I)} (F : MatchingBasisChoice a b)
    (μ : X) (t : F.Labels) (p : SYM D R) :
    homMap f D Sc _ _ (F.expansion cs μ (Finsupp.single t p)) =
      F.expansion (cScalars D f cs) μ
        (Finsupp.single t (symMap (D := D) f p)) := by
  rw [F.expansion_single, F.expansion_single, homMap_comp,
    homMap_bubAt, homMap_betaSYM, homMap_xev]

/-- The complete finite decorated matching expansion commutes with scalar
change. This is an image formula, not matching independence. -/
theorem homMap_expansion {a b : List (Letter I)} (F : MatchingBasisChoice a b)
    (μ : X) (z : F.Labels →₀ SYM D R) :
    homMap f D Sc _ _ (F.expansion cs μ z) =
      F.expansion (cScalars D f cs) μ
        (Finsupp.mapRange.addMonoidHom (symMap (D := D) f).toAddMonoidHom z) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add t p z h hp ih =>
      simp only [map_add, homMap_expansion_single, ih]
      change _ = F.expansion (cScalars D f cs) μ
        (Finsupp.mapRange (symMap (D := D) f) (map_zero _) (Finsupp.single t p)) + _
      rw [Finsupp.mapRange_single]

/-- The tensor comparison preserves each decorated matching with its full
polynomial/exterior coefficient, including odd bubbles. -/
theorem homBaseChange_expansion_single {a b : List (Letter I)}
    (F : MatchingBasisChoice a b) (μ : X) (s : S)
    (t : F.Labels) (p : SYM D R) :
    letI := f.toAlgebra
    homBaseChange f D Sc (ob D μ a) (ob D μ b)
      (s ⊗ₜ[R] F.expansion cs μ (Finsupp.single t p)) =
      s • F.expansion (cScalars D f cs) μ
        (Finsupp.single t (symMap (D := D) f p)) := by
  let := f.toAlgebra
  rw [homBaseChange_tmul, homMap_expansion_single]

end OddMath.SKM.ScalarChange
