/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Nondegeneracy
import Categorification.Diagrams.KL3.GdimBound

/-!
# Representatives of matchings and KL III pairings

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8 (the choice of
representatives before Theorem 8.1), and A. D. Lauda, M. Khovanov, *A categorification of quantum
sl(n)* III, arXiv:0807.3250, §2.2 (the pairings `p'(𝐢, 𝐣)`).

The representatives of a `MatchingBasisChoice` for `(a, b)` are in bijection with the
`(a, b)`-pairings of KL III (`MatchingBasisChoice.pairingEquiv`): a representative goes to the
matching of its pairing on the letters `a* b`, and `a*` (`dualW`) is KL's `ρW a`.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open StringDiagrams StringDiagrams.Chord
open Categorification.QuantumGroup

universe u

variable {I : Type u}

theorem dualW_eq_ρW (a : List (Letter I)) : dualW a = UDot.ρW a := rfl

variable {a b : List (Letter I)}

theorem valid_pairing₂ {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    Valid (pairing₂ a R) :=
  ((tInv_tStart a).run hR.1).valid

theorem letters_pairing₂ {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    (pairing₂ a R).map Prod.snd = dualW a ++ b := by
  rw [pairing₂, letters_tRun (length_dualW a) R _ a (tStart_letters a) hR.1, hR.2]

theorem lettered_pairing₂ {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    Lettered flipL (pairing₂ a R) := by
  obtain ⟨hf₀, -, -, -⟩ := cupMoves_spec (dualW a)
  exact lettered_tRun R _ (tInv_tStart a) (Chord.lettered_run flipL_involutive hf₀) hR.1

theorem length_pairing₂ {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    (pairing₂ a R).length = (UDot.ρW a ++ b).length := by
  have := congrArg List.length (letters_pairing₂ hR)
  rw [List.length_map] at this
  rw [this, dualW_eq_ρW]

/-- The KL labelling of the endpoints of `(a, b)`-pairings: the letters of `ρW a ++ b`. -/
abbrev klLabel (a b : List (Letter I)) (p : Fin (UDot.ρW a ++ b).length) :
    Letter I :=
  (UDot.ρW a ++ b).get p

theorem lettersOf_pairing₂ {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    lettersOf (pairing₂ a R) (length_pairing₂ hR) = klLabel a b := by
  funext p
  have h := congrArg (fun l => l[(p : ℕ)]?) (letters_pairing₂ hR)
  simp only [List.getElem?_map, dualW_eq_ρW] at h
  rw [List.getElem?_eq_getElem (by rw [length_pairing₂ hR]; exact p.2),
    List.getElem?_eq_getElem p.2] at h
  simpa [lettersOf, klLabel] using h

/-- The matching of the pairing of an `(a, b)`-matching, as a permutation of the endpoints of
`ρW a ++ b`. -/
def matchingPerm {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    Equiv.Perm (Fin (UDot.ρW a ++ b).length) :=
  matchingOf (valid_pairing₂ hR) (length_pairing₂ hR)

theorem flipL_lettersOf {s : List (ℕ × Letter I)} {n : ℕ} (hv : Valid s) (hn : s.length = n)
    (hl : Lettered flipL s) (p : Fin n) :
    lettersOf s hn (matchingOf hv hn p) = flipL (lettersOf s hn p) := by
  have hS := (same_iff_matchingOf hv hn p _).2 rfl
  have key : ∀ i j : Fin n, Same s i j → (i : ℕ) < j →
      lettersOf s hn j = flipL (lettersOf s hn i) := by
    intro i j h hlt
    have := hl i j h hlt
    rw [List.getElem?_eq_getElem (by rw [hn]; exact j.2),
      List.getElem?_eq_getElem (by rw [hn]; exact i.2)] at this
    simpa [lettersOf] using this
  rcases lt_or_gt_of_ne (show (p : ℕ) ≠ matchingOf hv hn p from hS.ne) with h | h
  · exact key _ _ hS h
  · rw [key _ _ hS.symm h, flipL_involutive]

theorem matchingPerm_mem_pairings {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    matchingPerm hR ∈ UDot.pairings a b := by
  rw [UDot.pairings, UDot.mem_matchings]
  intro p
  have h := flipL_lettersOf (valid_pairing₂ hR) (length_pairing₂ hR) (lettered_pairing₂ hR) p
  rw [lettersOf_pairing₂ hR] at h
  exact ⟨(isMatching_matchingOf _ _).involutive p, (congrArg Prod.snd h :),
    (congrArg Prod.fst h :)⟩

/-- A KL pairing is a fixed-point-free involution. -/
theorem isMatching_of_mem_pairings {σ : Equiv.Perm (Fin (UDot.ρW a ++ b).length)}
    (hσ : σ ∈ UDot.pairings a b) : IsMatching σ := by
  rw [UDot.pairings, UDot.mem_matchings]
    at hσ
  refine ⟨fun p => (hσ p).1, fun p hp => ?_⟩
  have := (hσ p).2.2
  rw [hp] at this
  cases h : ((UDot.ρW a ++ b).get p).1 <;> simp_all

theorem klLabel_apply_of_mem_pairings
    {σ : Equiv.Perm (Fin (UDot.ρW a ++ b).length)}
    (hσ : σ ∈ UDot.pairings a b) (p) :
    klLabel a b (σ p) = flipL (klLabel a b p) := by
  rw [UDot.pairings, UDot.mem_matchings]
    at hσ
  exact Prod.ext (hσ p).2.2 (hσ p).2.1

/-- Every KL pairing is the matching of a strictly reduced `(a, b)`-matching. -/
theorem exists_matchingPerm_eq
    {σ : Equiv.Perm (Fin (UDot.ρW a ++ b).length)}
    (hσ : σ ∈ UDot.pairings a b) :
    ∃ R, ∃ hR : IsMatching₂ a b R, StrictReduced₂ a R ∧ matchingPerm hR = σ := by
  have hm := isMatching_of_mem_pairings hσ
  have hv := valid_ofMatching (klLabel a b) hm
  have hl : Lettered flipL (ofMatching σ (klLabel a b)) :=
    lettered_ofMatching (klLabel a b) hm fun i _ => klLabel_apply_of_mem_pairings hσ i
  have hs : (ofMatching σ (klLabel a b)).map Prod.snd = dualW a ++ b := by
    rw [map_snd_ofMatching, dualW_eq_ρW]; exact List.ofFn_get _
  obtain ⟨R, hR, hred, hiso⟩ := exists_strictReduced_matching hv hl hs
  refine ⟨R, hR, hred, ?_⟩
  have := ((iso_iff (valid_pairing₂ hR) (length_pairing₂ hR) hv
    (length_ofMatching σ (klLabel a b))).1 hiso).1
  rw [matchingOf_ofMatching hm] at this
  exact this

theorem isLeftEnd_iff_lt_matchingPerm {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    (p : Fin (UDot.ρW a ++ b).length) :
    IsLeftEnd (pairing₂ a R) p ↔ p < matchingPerm hR p := by
  have hS := (same_iff_matchingOf (valid_pairing₂ hR) (length_pairing₂ hR) p _).2 rfl
  have hlen : (p : ℕ) < (pairing₂ a R).length := by rw [length_pairing₂ hR]; exact p.2
  constructor
  · rintro ⟨-, h⟩
    rcases lt_or_gt_of_ne (show (p : ℕ) ≠ matchingPerm hR p from hS.ne) with h' | h'
    · exact h'
    · exact absurd ⟨_, h', hS⟩ h
  · intro h
    refine ⟨hlen, fun ⟨j', hj', hS'⟩ => ?_⟩
    have := (valid_pairing₂ hR).unique hS hS'
    change ((matchingPerm hR p : ℕ)) = j' at this
    have h2 : ((matchingPerm hR p : ℕ)) < p := this ▸ hj'
    exact absurd (lt_trans h h2) (lt_irrefl _)

/-- **The strands of a matching are the arcs of its KL pairing**: a strand, named by its left
endpoint `j`, is the arc starting at `j`. -/
def strandEquivArc {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    MatchingStrand a R ≃ Categorification.KL3.Diagram.Arc a b (matchingPerm hR) where
  toFun j := ⟨⟨j.1, by
      have := (mem_leftEnds₂.1 j.2).1; rwa [length_pairing₂ hR] at this⟩,
    (isLeftEnd_iff_lt_matchingPerm hR _).1 (mem_leftEnds₂.1 j.2)⟩
  invFun x := ⟨x.1.1, mem_leftEnds₂.2 ((isLeftEnd_iff_lt_matchingPerm hR x.1).2 x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The colour of a strand is the colour of its arc. -/
theorem arcCol_strandEquivArc {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    (j : MatchingStrand a R) :
    Categorification.KL3.Diagram.arcCol (strandEquivArc hR j) =
      (lettersOf (pairing₂ a R) (length_pairing₂ hR) (strandEquivArc hR j).1).2 := by
  rw [lettersOf_pairing₂ hR]; rfl

end OddMath.SKM.EvenBridge

namespace OddMath.SKM.MatchingBasisChoice

open StringDiagrams StringDiagrams.Chord Categorification.QuantumGroup EvenBridge

variable {I : Type u} {a b : List (Letter I)} (F : MatchingBasisChoice a b)

/-- **The representatives of a matching basis choice are the KL III pairings** `p'(a, b)`:
a representative goes to the matching of its pairing. -/
def pairingEquiv : F.members ≃ UDot.pairings a b :=
  Equiv.ofBijective (fun R => ⟨matchingPerm (F.matching R R.2).1,
      matchingPerm_mem_pairings (F.matching R R.2).1⟩) <| by
    constructor
    · rintro ⟨R, hR⟩ ⟨S, hS⟩ h
      have h := congrArg Subtype.val h
      refine Subtype.ext (F.unique R hR S hS ((iso_iff (valid_pairing₂ (F.matching R hR).1)
        (length_pairing₂ (F.matching R hR).1) (valid_pairing₂ (F.matching S hS).1)
        (length_pairing₂ (F.matching S hS).1)).2 ⟨h, ?_⟩))
      rw [lettersOf_pairing₂ (F.matching R hR).1, lettersOf_pairing₂ (F.matching S hS).1]
    · rintro ⟨σ, hσ⟩
      obtain ⟨R, hR, hred, e⟩ := exists_matchingPerm_eq hσ
      obtain ⟨S, hS, hiso⟩ := F.complete R hR hred
      refine ⟨⟨S, hS⟩, Subtype.ext ?_⟩
      show matchingPerm (F.matching S hS).1 = σ
      rw [← e]
      exact ((iso_iff (valid_pairing₂ (F.matching S hS).1) (length_pairing₂ (F.matching S hS).1)
        (valid_pairing₂ hR) (length_pairing₂ hR)).1 hiso).1

theorem pairingEquiv_apply (R : F.members) :
    (F.pairingEquiv R : Equiv.Perm _) = matchingPerm (F.matching R R.2).1 := rfl

end OddMath.SKM.MatchingBasisChoice
