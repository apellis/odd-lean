/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapFamily
import OddMath.SKM.DecoratedNormalization

/-! Strand and natural-label transport for adjacent cap deletion in the
cap class of BE2 Theorem 10.3, Claim 5. No grading assertion is made. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

/-- Endpoint coordinate after removing the adjacent positions `p,p+1`. -/
def capDown (p j : ℕ) : ℕ := if j < p then j else j - 2

@[simp] theorem capDown_rmIdx (p j : ℕ) : capDown p (rmIdx p j) = j := by
  unfold capDown rmIdx
  split_ifs <;> omega

theorem rmIdx_capDown {p j : ℕ} (h₀ : j ≠ p) (h₁ : j ≠ p + 1) :
    rmIdx p (capDown p j) = j := by
  unfold capDown rmIdx
  split_ifs <;> omega

theorem cap_isLeftEnd {s : List (ℕ × Letter I)} {p : ℕ}
    (hv : Valid s) (hc : Same s p (p + 1)) : IsLeftEnd s p := by
  refine ⟨hc.lt_left, ?_⟩
  rintro ⟨k, hk, hs⟩
  have := hv.unique hc hs
  omega

/-- Removal preserves exactly the surviving left endpoints. -/
theorem isLeftEnd_rmAt_cap {s : List (ℕ × Letter I)} {p j : ℕ}
    (hv : Valid s) (hc : Same s p (p + 1)) :
    IsLeftEnd (rmAt s p) j ↔ IsLeftEnd s (rmIdx p j) := by
  have hp : p + 2 ≤ s.length := hc.lt_right
  constructor
  · rintro ⟨hj, hn⟩
    have hlen := length_rmAt s hp
    refine ⟨by rw [hlen] at hj; unfold rmIdx; split_ifs <;> omega, ?_⟩
    rintro ⟨k, hk, hs⟩
    have hk₀ : k ≠ p := by
      intro he
      rw [he] at hs
      have := hv.unique hc hs.symm
      unfold rmIdx at this
      split_ifs at this <;> omega
    have hk₁ : k ≠ p + 1 := by
      intro he
      rw [he] at hs
      have := hv.unique hc.symm hs.symm
      unfold rmIdx at this
      split_ifs at this <;> omega
    have he := rmIdx_capDown hk₀ hk₁
    apply hn
    refine ⟨capDown p k, (rmIdx_lt_iff p).mp (by simpa only [he] using hk), ?_⟩
    rw [same_rmAt hp, he]
    exact hs
  · rintro ⟨hj, hn⟩
    refine ⟨?_, ?_⟩
    · rw [length_rmAt s hp]
      unfold rmIdx at hj
      split_ifs at hj <;> omega
    · rintro ⟨k, hk, hs⟩
      exact hn ⟨rmIdx p k, (rmIdx_lt_iff p).mpr hk, (same_rmAt hp).mp hs⟩

/-- The distinguished cap strand, named by its left endpoint. -/
def capStrand {A : List (Letter I)} {R : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R))
    (hc : Same (pairing₂ A R) p (p + 1)) : MatchingStrand A R :=
  ⟨p, mem_leftEnds₂.mpr (cap_isLeftEnd hv hc)⟩

/-- Insert the two deleted endpoint positions in a shorter strand. -/
def capRemainingStrand {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R))
    (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p))
    (j : MatchingStrand B S) : MatchingStrand A R :=
  ⟨rmIdx p j.val, mem_leftEnds₂.mpr ((isLeftEnd_rmAt_cap hv hc).mp
    ((isLeftEnd_iso hi).mp (mem_leftEnds₂.mp j.property)))⟩

/-- Literal cap deletion splits the strand set into the cap and the shorter strands. -/
def matchingStrandEquivOfCap {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R))
    (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) :
    MatchingStrand A R ≃ Unit ⊕ MatchingStrand B S where
  toFun j := if he : j.val = p then Sum.inl () else Sum.inr ⟨capDown p j.val, by
    have hj := mem_leftEnds₂.mp j.property
    have hn : j.val ≠ p + 1 := by
      intro h
      apply hj.2
      exact ⟨p, by omega, h ▸ hc.symm⟩
    apply mem_leftEnds₂.mpr
    apply (isLeftEnd_iso hi).mpr
    apply (isLeftEnd_rmAt_cap hv hc).mpr
    simpa only [rmIdx_capDown he hn] using hj⟩
  invFun := Sum.elim (fun _ => capStrand hv hc) (capRemainingStrand hv hc hi)
  left_inv j := by
    dsimp
    split_ifs with he
    · exact Subtype.ext he.symm
    · apply Subtype.ext
      apply rmIdx_capDown he
      intro h
      exact (mem_leftEnds₂.mp j.property).2 ⟨p, by omega, h ▸ hc.symm⟩
  right_inv j := by
    rcases j with u | j
    · cases u
      simp [capStrand]
    · have hn : rmIdx p j.val ≠ p := by unfold rmIdx; split_ifs <;> omega
      simp [capRemainingStrand, hn]

/-- Membership formulation of the surviving endpoint transport. -/
theorem mem_leftEnds₂_cap {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p j : ℕ} (hv : Valid (pairing₂ A R))
    (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) :
    j ∈ leftEnds₂ B S ↔ rmIdx p j ∈ leftEnds₂ A R := by
  rw [mem_leftEnds₂, mem_leftEnds₂, isLeftEnd_iso hi, isLeftEnd_rmAt_cap hv hc]

@[simp] theorem matchingStrandEquivOfCap_cap
    {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) :
    matchingStrandEquivOfCap hv hc hi (capStrand hv hc) = Sum.inl () := by
  simp [matchingStrandEquivOfCap, capStrand]

@[simp] theorem matchingStrandEquivOfCap_remaining
    {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) (j : MatchingStrand B S) :
    matchingStrandEquivOfCap hv hc hi (capRemainingStrand hv hc hi j) = Sum.inr j :=
  (matchingStrandEquivOfCap hv hc hi).apply_symm_apply (Sum.inr j)

/-- Every surviving strand keeps its colour at the shifted endpoint. -/
theorem matchingStrandColour_capRemaining
    {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) (j : MatchingStrand B S) :
    matchingStrandColour A R (capRemainingStrand hv hc hi j) = matchingStrandColour B S j := by
  have he := congrArg (fun l : List (Letter I) => l[j.val]?) hi.1
  rw [List.getElem?_map, List.getElem?_map, getElem?_rmAt _ hc.lt_right] at he
  have hj := (mem_leftEnds₂.mp j.property).1
  have hk := (mem_leftEnds₂.mp (capRemainingStrand hv hc hi j).property).1
  change rmIdx p j.val < (pairing₂ A R).length at hk
  simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk,
    Option.map_some, Option.some.injEq] at he
  exact congrArg Prod.snd he.symm

/-- The summand removed from either cap orientation has the cap colour. -/
theorem matchingStrandColour_cap (a b : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)) :
    matchingStrandColour _ R (capStrand hR.pairing_properties.1 hc) = i := by
  have he := congrArg (fun l : List (Letter I) => l[b.length]?) hR.pairing_properties.2.2
  simp only [List.getElem?_map, List.getElem?_eq_getElem hc.lt_left, Option.map_some] at he
  have hs : (dualW (a ++ (ε, i) :: (!ε, i) :: b) ++ [])[b.length]? = some (ε, i) := by
    simp only [List.append_nil, dualW_append, dualW_cons, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [← length_dualW b]
    simp [flipL]
  rw [hs] at he
  exact congrArg Prod.snd (Option.some.inj he)

/-- Split every natural strand label into the cap count and shorter labels.
The inverse assigns the first coordinate to the cap and the second to each
surviving strand, using the endpoint decomposition rather than an enumeration. -/
def capLabelEquiv {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) :
    (MatchingStrand A R → ℕ) ≃ ℕ × (MatchingStrand B S → ℕ) where
  toFun c := (c (capStrand hv hc), fun j => c (capRemainingStrand hv hc hi j))
  invFun z j := Sum.elim (fun _ => z.1) z.2 (matchingStrandEquivOfCap hv hc hi j)
  left_inv c := by
    funext j
    change Sum.elim _ _ (matchingStrandEquivOfCap hv hc hi j) = c j
    have hj := (matchingStrandEquivOfCap hv hc hi).symm_apply_apply j
    generalize he : matchingStrandEquivOfCap hv hc hi j = z at *
    rcases z with u | k
    · cases u
      exact congrArg c hj
    · exact congrArg c hj
  right_inv z := by
    rcases z with ⟨n, c⟩
    apply Prod.ext
    · simp
    · funext j
      simp

@[simp] theorem capLabelEquiv_cap {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p)) (c : MatchingStrand A R → ℕ) :
    (capLabelEquiv hv hc hi c).1 = c (capStrand hv hc) := rfl

@[simp] theorem capLabelEquiv_remaining {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p))
    (c : MatchingStrand A R → ℕ) (j : MatchingStrand B S) :
    (capLabelEquiv hv hc hi c).2 j = c (capRemainingStrand hv hc hi j) := rfl

@[simp] theorem capLabelEquiv_symm_cap {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p))
    (n : ℕ) (c : MatchingStrand B S → ℕ) :
    (capLabelEquiv hv hc hi).symm (n, c) (capStrand hv hc) = n := by
  simp [capLabelEquiv]

@[simp] theorem capLabelEquiv_symm_remaining {A B : List (Letter I)}
    {R S : List (TMove (Letter I))} {p : ℕ}
    (hv : Valid (pairing₂ A R)) (hc : Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (rmAt (pairing₂ A R) p))
    (n : ℕ) (c : MatchingStrand B S → ℕ) (j : MatchingStrand B S) :
    (capLabelEquiv hv hc hi).symm (n, c) (capRemainingStrand hv hc hi j) = c j := by
  simp [capLabelEquiv]

/-- Lift a representative correspondence whose pairings realize cap deletion
through the constructed strand and label maps. -/
def capFamilyLabelEquiv {a b : List (Letter I)} {ε : Bool} {i : I}
    {M N : Set (List (TMove (Letter I)))}
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (E : {R // R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)} ≃
        {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ (a ++ b) (E R).val)
      (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val) b.length)) :
    (Σ R : {R // R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)},
        MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) ≃
      ℕ × (Σ S : {S // S ∈ N}, MatchingStrand (a ++ b) S.val → ℕ) :=
  (Equiv.sigmaCongr E (fun R => capLabelEquiv
    (hM R R.property.1).pairing_properties.1 R.property.2 (hE R))).trans
      { toFun (z : Σ S : {S // S ∈ N}, ℕ × (MatchingStrand (a ++ b) S.val → ℕ)) :=
          (z.2.1, ⟨z.1, z.2.2⟩)
        invFun z := ⟨z.2.1, z.1, z.2.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }

/-- Complete unique strict-reduced families yield the cap-count/shorter-label
correspondence. The representative equivalence and its pairing transport are
constructed by deletion and insertion; no strand or label bijection is assumed. -/
theorem cap_labelled_representatives_equiv (a b : List (Letter I)) (ε : Bool) (i : I)
    (M N : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R ∧
      StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
    (hN : ∀ S ∈ N, IsMatching₂ (a ++ b) [] S ∧ StrictReduced₂ (a ++ b) S)
    (hMrep : ∀ R, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R →
      StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S)
        (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ b) [] R → StrictReduced₂ (a ++ b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ b) S) (pairing₂ (a ++ b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
        (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ b) R) (pairing₂ (a ++ b) S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M ∧
        Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)},
          MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) ≃
        ℕ × (Σ S : {S // S ∈ N}, MatchingStrand (a ++ b) S.val → ℕ),
      ∀ R c, (F ⟨R, c⟩).1 =
        c (capStrand (hM R R.property.1).1.pairing_properties.1 R.property.2) := by
  obtain ⟨E, hE, _⟩ := cap_representatives_equiv a b ε i M N hM hN hMrep hNrep hMuniq hNuniq
  exact ⟨capFamilyLabelEquiv (fun R h => (hM R h).1) E hE, fun _ _ => rfl⟩

end OddMath.SKM
