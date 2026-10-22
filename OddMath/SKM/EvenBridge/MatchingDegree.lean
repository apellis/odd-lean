/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.ChordDegree
import OddMath.SKM.EvenBridge.Pairings
import OddMath.SKM.TwoSidedGrading
import Categorification.Diagrams.KL3.NondegPositive

/-!
# Degrees of reduced matchings in `𝔘(𝔤)` and in KL III's `U`

For purely even data with KL scalars, the degree ([BE2] (1.13), arXiv:1701.04133v2) of the
layered diagram of a reduced `(a, b)`-matching is KL III's degree `deg(D_σ, λ)` of the minimal
diagram of the corresponding `(a, b)`-pairing (Khovanov–Lauda, *A categorification of quantum
sl(n)*, arXiv:0807.3250v1, §2.2 and Def. 3.1), with `λ` the weight of the rightmost region.

## Main results

* `tableDegree_cupA`: the nested cups have the same degree in both calculi.
* `tableDegree_tLay`: the degree of `tLay a R` for a reduced matching `R` is `pdeg` of the
  pairing `matchingPerm hR`.
-/

noncomputable section
namespace OddMath.SKM.EvenBridge
open StringDiagrams StringDiagrams.Chord Categorification.KL3 Categorification.QuantumGroup

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : CartanDatum I) (hc : Compatible D C)

local notation "RD" => weightDatum D C hc

/-- The nested cups `1 → w w*` have the same degree in `𝔘(𝔤)` and in `U`. -/
theorem tableDegree_cupA (μ : X) : ∀ w : List (Letter I),
    tableDegree D (symmetrizer D C hc) μ (cupA w) = Diagram.sdegSum RD μ (Diagram.cupA w)
  | [] => rfl
  | l :: w => by
    have hcons : ∀ (x : Diagram.LayerData I) (L : List (Diagram.LayerData I)),
        Diagram.sdegSum RD μ (x :: L) = Diagram.sdegSum RD μ [x] + Diagram.sdegSum RD μ L :=
      fun x L => by rw [← Diagram.sdegSum_append]; rfl
    rw [cupA, Diagram.cupA, tableDegree_append, tableDegree_whisk, tableDegree_cupA _ w, hcons,
      Diagram.sdegSum_map_whL, wt_eq D C hc]
    congr 1
    · simp only [tableDegree_cup, Diagram.sdegSum, Diagram.sdeg, symmetrizer_d, wt_eq D C hc,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      obtain ⟨_ | _, i⟩ := l
      · simp [UDot.sgn, weightDatum_pair]
      · simp [UDot.sgn, weightDatum_pair]
        ring_nf
        simp

variable {a b : List (Letter I)}

/-- The signed colour sum of a word with a pairing vanishes. -/
theorem aS_eq_zero_of_isMatching {w : List (Letter I)} {σ : Equiv.Perm (Fin w.length)}
    (hσ : UDot.IsMatching (fun p => w.get p) σ) (i : I) : UDot.aS C i w = 0 := by
  have h := hσ.sum_cancel Finset.univ (fun r => UDot.sgn (w.get r).1 * UDot.A C i (w.get r).2)
    (fun r => by rw [hσ.sgn_eq, hσ.col]; ring)
  simp only [Finset.mem_univ, not_true_eq_false, Finset.filter_false, Finset.sum_empty] at h
  rw [UDot.aS, ← Fin.sum_univ_fun_getElem]
  simpa using h

/-- **The degree of a reduced matching** is KL III's degree of the minimal diagram of its
pairing. -/
theorem tableDegree_tLay (μ : X) {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    (hred : Reduced₂ a R) :
    tableDegree D (symmetrizer D C hc) μ (tLay a R) =
      UDot.pdeg C ((RD).ellOf μ) a b (matchingPerm hR) := by
  have H := (reduced₂_bent_degree_parity D (symmetrizer D C hc) μ hR hred).1
  rw [tableDegree_append, tableDegree_whisk, wt_nil, tableDegree_cupA, tableDegree_chordLay,
    show dualW a = Diagram.rd a from rfl, Diagram.sdegSum_cupA_rd,
    Diagram.sdegSum_canon μ _ (Nat.lt_succ_self _) (valid_pairing₂ hR) (lettered_pairing₂ hR)
      (length_pairing₂ hR), lettersOf_pairing₂ hR] at H
  have hm : UDot.IsMatching (klLabel a b) (matchingPerm hR) :=
    UDot.mem_matchings.1 (matchingPerm_mem_pairings hR)
  have hw : UDot.wl C ((RD).ellOf μ) b = fun i => Diagram.ip RD i (Diagram.wt RD μ a) := by
    rw [← Diagram.wl_ellOf_eq']
    funext i
    have h0 := aS_eq_zero_of_isMatching C hm i
    rw [UDot.aS_append, UDot.aS_ρW] at h0
    simp only [UDot.wl]
    linarith
  rw [UDot.pdeg, UDot.bendDeg_eq_rcx, hw]
  change _ = UDot.mdeg C _ (klLabel a b) (matchingOf (valid_pairing₂ hR) (length_pairing₂ hR)) + _
  linarith

end OddMath.SKM.EvenBridge
