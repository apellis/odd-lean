/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AlphaPositional
import OddMath.QuiverHecke.UpwardPBWCoordinates
import OddMath.SKM.BottomMatchingChoice
import OddMath.SKM.MatchingChoiceTransition

/-! # Exact comparison of canonical upward matching choices with affine PBW -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams StringDiagrams.Chord Categorification.TypeA
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

theorem upWord_tgt_decorated (t : List I) (gs : List PG)
    (hg : ∀ g ∈ gs, g.pos + g.width ≤ t.length) :
    (SKM.DTMove.tmoves (gs.map PG.toDTMove)).foldl SKM.tLet (upWord t) = upWord (tgt t gs) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    have htail : ∀ h ∈ gs, h.pos + h.width ≤ (g.act t).length := by
      intro h hh
      simpa only [length_act] using hg h (List.mem_cons_of_mem g hh)
    have hhead := hg g List.mem_cons_self
    cases g with
    | dot p => simpa only [List.map_cons, PG.toDTMove, SKM.DTMove.tmoves, tgt_cons, PG.act] using ih t htail
    | cross p =>
      have hp : p + 1 < t.length := by simp only [PG.pos, PG.width] at hhead; omega
      simpa only [List.map_cons, PG.toDTMove, SKM.DTMove.tmoves, List.foldl_cons,
        ← upWord_cross_act hp, tgt_cons] using ih ((PG.cross p).act t) htail

theorem canonical_cw_valid (t : List I) (w : Equiv.Perm (Fin t.length)) :
    ∀ g ∈ cw (canWord t.length w), g.pos + g.width ≤ t.length := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
  have hv := validWord_canWord t.length w p (List.mem_reverse.mp hp)
  simp only [PG.pos, PG.width]
  omega

variable {t t' : List I}
variable (F : SKM.MatchingBasisChoice (upWord t) (upWord t'))
variable (w : F.members → Equiv.Perm (Fin t.length))
variable (hR : ∀ R : F.members,
  R.val = (canWord t.length (w R)).reverse.map (fun p => TMove.mv (Move.cross p)))

include hR

theorem canonical_matching_tgt (R : F.members) : tgt t (cw (canWord t.length (w R))) = t' := by
  have he := upWord_tgt_decorated t (cw (canWord t.length (w R))) (canonical_cw_valid t (w R))
  have hm : SKM.DTMove.tmoves ((cw (canWord t.length (w R))).map PG.toDTMove) = R.val := by
    rw [hR R]
    simpa only [cw, List.map_map, Function.comp_def, PG.toDTMove] using
      SKM.DTMove.tmoves_map_tm ((canWord t.length (w R)).reverse.map (fun p => TMove.mv (Move.cross p)))
  rw [hm, (F.matching R.val R.property).1.2] at he
  have he' := congrArg (List.map Prod.snd) he
  simpa [upWord, SKM.up, List.map_map, Function.comp_def] using he'.symm

def canonicalChoiceIndex (z : (F.atBottomSortedUp t t').Labels) : NFIdx t t' := by
  let dots := F.bottomPositions z.1 z.2
  refine ⟨(dots, w z.1), F.bottomPositions_pairwise _ _, ?_, ?_⟩
  · simpa only [upWord, List.length_map] using F.bottomPositions_bound (F.positive_bottom_bound t t') z.1 z.2
  · have hc := sChain_pl t (dots.map PG.dot ++ cw (canWord t.length (w z.1)))
    rw [tgt_append, tgt_map_dot, canonical_matching_tgt F w hR] at hc
    exact hc

theorem canonicalChoiceIndex_injective : Function.Injective (canonicalChoiceIndex F w hR) := by
  rintro ⟨R, n⟩ ⟨S, m⟩ he
  have hw : w R = w S := congrArg (fun i : NFIdx t t' => i.1.2) he
  have hrs : R = S := Subtype.ext ((hR R).trans (by rw [hw, ← hR S]))
  subst S
  have hd := congrArg (fun i : NFIdx t t' => i.1.1) he
  have hn := F.bottomPositions_injective (F.positive_bottom_bound t t') R hd
  change n = m at hn
  subst m
  rfl

theorem canonicalChoiceIndex_evaluation (μ : X) (z : (F.atBottomSortedUp t t').Labels) :
    (alpha D Sc μ).map ((canonicalChoiceIndex F w hR z).nf (D := D) (Sc := Sc)) =
      SKM.xev cs μ (upWord t) (upWord t') ((F.atBottomSortedUp t t').layers z) := by
  rw [alpha_nf_eq_xev D Sc cs]
  congr 1
  change SKM.dLay (upWord t)
    (((F.bottomPositions z.1 z.2).map PG.dot ++ cw (canWord t.length (w z.1))).map PG.toDTMove) =
    SKM.dLay (upWord t) ((F.bottomPositions z.1 z.2).map SKM.DTMove.dt ++ z.1.val.map SKM.DTMove.tm)
  rw [hR z.1]
  simp only [List.map_append, List.map_map, cw]
  rfl

def canonicalChoiceReindex :
    ((F.atBottomSortedUp t t').Labels →₀ SKM.SYM D k) →ₗ[k] (NFIdx t t' →₀ SKM.SYM D k) :=
  Finsupp.lmapDomain (SKM.SYM D k) k (canonicalChoiceIndex F w hR)

theorem canonicalChoiceReindex_injective : Function.Injective (canonicalChoiceReindex (k := k) D F w hR) :=
  Finsupp.mapDomain_injective (canonicalChoiceIndex_injective F w hR)

theorem canonicalChoice_expansion (μ : X)
    (f : (F.atBottomSortedUp t t').Labels →₀ SKM.SYM D k) :
    (F.atBottomSortedUp t t').expansion cs μ f =
      upwardPBWExpansion D Sc cs μ t t' (canonicalChoiceReindex D F w hR f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single z a =>
    rw [SKM.MatchingBasisChoice.expansion_single]
    simp only [canonicalChoiceReindex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      upwardPBWExpansion_single]
    rw [canonicalChoiceIndex_evaluation D Sc cs F w hR]
    rfl

/-- A canonical crossing family needs no matching-independence premise:
native affine PBW coordinates and the actual upward map suffice. -/
theorem canonicalChoice_independence (μ : X)
    (hUp : Function.Injective (upwardCoefficientMap D Sc cs μ t t')) :
    Function.Injective (F.expansion cs μ) := by
  apply F.expansion_injective_of_choice cs μ (F.atBottomSortedUp t t')
  intro f g he
  apply canonicalChoiceReindex_injective D F w hR
  apply (hUp.comp (coefficientPBWExpansion_injective D Sc t t'))
  change upwardPBWExpansion D Sc cs μ t t' (canonicalChoiceReindex D F w hR f) =
    upwardPBWExpansion D Sc cs μ t t' (canonicalChoiceReindex D F w hR g)
  rw [← canonicalChoice_expansion D Sc cs F w hR,
    ← canonicalChoice_expansion D Sc cs F w hR]
  exact he

end OddMath.QuiverHecke
