import OddMath.SKM.CupAttachment

/-! Crossing-minimality of literal cup attachment, supporting BE2 v2 Theorem 10.3
Claim 2. This does not impose or preserve the additional critical-point condition
of BE2 §8, nor assert normalized-family degree or parity invariance. -/

namespace StringDiagrams.Chord

/-- Every interleaving pair contributes a crossing to the actual crossing list. -/
theorem cr_le_length_xs {α : Type*} {T : TState α} (I : TInv T) :
    cr T.st ≤ T.xs.length := by
  classical
  let f : ℕ × ℕ × ℕ × ℕ → Sym2 ℕ := fun q => s(idD T.st q.1, idD T.st q.2.1)
  have hsub : (crSet T.st).image f ⊆ T.xs.toFinset := by
    intro z hz
    obtain ⟨⟨i, j, k, l⟩, hq, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hij, hjk, hkl, hik, hjl⟩ : Cr4 T.st i j k l := mem_crSet.1 hq
    have hi := idAt_eq_idD hik.lt_left
    have hj := idAt_eq_idD hjl.lt_left
    have hne : idD T.st i ≠ idD T.st j := by
      intro e
      have hs : Same T.st i j :=
        ⟨by omega, idAt_ne_none_iff.2 hik.lt_left, by rw [hi, hj, e]⟩
      have := I.valid.unique hik hs
      omega
    have hil : Ilv2 T.st (idD T.st i) (idD T.st j) :=
      Or.inl ⟨i, j, k, l, ⟨hij, hjk, hkl, hik, hjl⟩, hi, hj⟩
    exact List.mem_toFinset.2 (List.count_pos_iff.1 ((I.parity _ _ hne).1 hil).pos)
  calc
    cr T.st = ((crSet T.st).image f).card :=
      (Finset.card_image_of_injOn (injOn_crSet I.valid)).symm
    _ ≤ T.xs.toFinset.card := Finset.card_le_card hsub
    _ ≤ T.xs.length := List.toFinset_card_le _

end StringDiagrams.Chord

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

/-- Position shifting and the new cup leave the actual number of crossings unchanged. -/
@[simp] theorem ncr₂_cupAttachMatching (i : I) (R : List (TMove (Letter I))) :
    ncr₂ (cupAttachMatching i R) = ncr₂ R := by
  simp only [cupAttachMatching, ncr₂, List.countP_cons, List.countP_map,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  congr 1
  funext m
  rcases m with (⟨g, x⟩ | p) | g <;> rfl

/-- Literal right-cup attachment preserves crossing-minimality. Critical points are
unrestricted: an attached cap can become a zigzag. This is the geometric prerequisite
for BE2 v2 Theorem 10.3 Claim 2, not the normalized-family comparison itself. -/
theorem reduced₂_cupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R)
    (hred : Reduced₂ ((true, i) :: a) R) :
    Reduced₂ a (cupAttachMatching i R) := by
  obtain ⟨hm, hi⟩ := cupAttach_matching_iso hR
  have hOld := (tInv_tStart ((true, i) :: a)).run hR.1
  have hNew := (tInv_tStart a).run hm.1
  have hup := Chord.length_xs_le_cr hOld hred.1 hred.2
  have hlo := Chord.cr_le_length_xs hNew
  have hcount :
      (tRun flipL a.length (tStart a) (cupAttachMatching i R)).xs.length =
        (tRun flipL ((true, i) :: a).length (tStart ((true, i) :: a)) R).xs.length := by
    simp only [Chord.length_xs_tRun, ncr₂_cupAttachMatching]
    rfl
  have hcr : cr (pairing₂ a (cupAttachMatching i R)) =
      cr (pairing₂ ((true, i) :: a) R) :=
    le_antisymm (Chord.cr_le_of_iso hi) (Chord.cr_le_of_iso hi.symm)
  apply Chord.reduced_of_length_xs_eq_cr hNew
  apply le_antisymm _ hlo
  rw [hcount]
  exact hup.trans (le_of_eq hcr.symm)

end OddMath.SKM
