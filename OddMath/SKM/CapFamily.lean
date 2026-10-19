import OddMath.SKM.PositiveMatchings

/-! The cap class in BE2 v2 Theorem 10.3 Claim 5: deletion and insertion of
an adjacent paired pair of endpoints, followed by strict realization. This
module concerns representatives only, not decorations or graphical degrees. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

/-- Deleting the distinguished cap leaves the shorter dual boundary. -/
theorem cap_deleted_properties (a b : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)) :
    Valid (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length) ∧
    Lettered flipL (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length) ∧
    (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length).map Prod.snd =
      dualW (a ++ b) ++ [] := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  refine ⟨hv.rmAt hc, hl.rmAt hc.lt_right, ?_⟩
  rw [map_rmAt, hs]
  simp only [List.append_nil, dualW_append, dualW_cons, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [← length_dualW b]
  simp [rmAt]

/-- A cap-class matching gives a strict realization of its deleted pairing. -/
theorem exists_strictReduced_cap_delete (a b : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)) :
    ∃ S, IsMatching₂ (a ++ b) [] S ∧ StrictReduced₂ (a ++ b) S ∧
      Iso (pairing₂ (a ++ b) S)
        (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length) := by
  obtain ⟨hv, hl, hs⟩ := cap_deleted_properties a b ε i hR hc
  exact exists_strictReduced_matching hv hl hs

/-- Insert a fresh paired pair at the reversed boundary position. -/
def capInsertedPairing (a b : List (Letter I)) (ε : Bool) (i : I)
    (S : List (TMove (Letter I))) : List (ℕ × Letter I) :=
  let T := tRun flipL (a ++ b).length (tStart (a ++ b)) S
  insAt T.st b.length (T.nxt, (ε, i)) (T.nxt, (!ε, i))

theorem cap_inserted_properties (a b : List (Letter I)) (ε : Bool) (i : I)
    {S : List (TMove (Letter I))} (hS : IsMatching₂ (a ++ b) [] S) :
    Valid (capInsertedPairing a b ε i S) ∧
    Lettered flipL (capInsertedPairing a b ε i S) ∧
    (capInsertedPairing a b ε i S).map Prod.snd =
      dualW (a ++ (ε, i) :: (!ε, i) :: b) ++ [] ∧
    Same (capInsertedPairing a b ε i S) b.length (b.length + 1) ∧
    rmAt (capInsertedPairing a b ε i S) b.length = pairing₂ (a ++ b) S := by
  obtain ⟨hv, hl, hs⟩ := hS.pairing_properties
  have hb : b.length ≤ (pairing₂ (a ++ b) S).length := by
    have := congrArg List.length hs
    simp only [List.length_map, List.length_append, length_dualW, List.length_nil] at this
    omega
  have hf := ((tInv_tStart (a ++ b)).run hS.1).fresh
  change (∀ x ∈ pairing₂ (a ++ b) S,
    x.1 < (tRun flipL (a ++ b).length (tStart (a ++ b)) S).nxt) at hf
  have hn := fun x hx => (hf x hx).ne
  change Valid (insAt _ _ _ _) ∧ Lettered flipL (insAt _ _ _ _) ∧ _
  refine ⟨hv.insAt hb hn _ _, hl.insAt flipL_involutive hb hn (ε, i), ?_,
    (same_insAt_iff hb hn _ _).mpr (Or.inl ⟨rfl, rfl⟩), rmAt_insAt _ _ _ _ hb⟩
  change (insAt (pairing₂ (a ++ b) S) b.length _ _).map Prod.snd = _
  rw [map_insAt, hs]
  simp only [List.append_nil, dualW_append, dualW_cons, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [← length_dualW b]
  simp [insAt, flipL]

/-- Strict realization of cap insertion, with the distinguished cap retained. -/
theorem exists_strictReduced_cap_insert (a b : List (Letter I)) (ε : Bool) (i : I)
    {S : List (TMove (Letter I))} (hS : IsMatching₂ (a ++ b) [] S) :
    ∃ R, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R ∧
      StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R ∧
      Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) (capInsertedPairing a b ε i S) := by
  obtain ⟨hv, hl, hs, _⟩ := cap_inserted_properties a b ε i hS
  exact exists_strictReduced_matching hv hl hs

/-- Equal deleted pairings and equal boundary letters reconstruct the cap pairing.
The removed arc ids are fresh in the remainder by validity. -/
theorem cap_iso_of_deleted {s t : List (ℕ × Letter I)} {p : ℕ}
    (hs : Valid s) (ht : Valid t) (hsc : Same s p (p + 1)) (htc : Same t p (p + 1))
    (hl : s.map Prod.snd = t.map Prod.snd) (hi : Iso (rmAt s p) (rmAt t p)) : Iso s t := by
  have hid {u : List (ℕ × Letter I)} (h : Same u p (p + 1)) :
      (u[p + 1]'h.lt_right).1 = (u[p]'h.lt_left).1 := by
    have he := h.2.2
    simpa only [idAt, List.getElem?_eq_getElem h.lt_left,
      List.getElem?_eq_getElem h.lt_right, Option.map_some, Option.some.injEq] using he.symm
  have hleft : (s[p]'hsc.lt_left).2 = (t[p]'htc.lt_left).2 := by
    have he := congrArg (fun l : List (Letter I) => l[p]?) hl
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hsc.lt_left,
      List.getElem?_eq_getElem htc.lt_left, Option.map_some, Option.some.injEq] using he
  have hright : (s[p + 1]'hsc.lt_right).2 = (t[p + 1]'htc.lt_right).2 := by
    have he := congrArg (fun l : List (Letter I) => l[p + 1]?) hl
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hsc.lt_right,
      List.getElem?_eq_getElem htc.lt_right, Option.map_some, Option.some.injEq] using he
  have hb : p ≤ (rmAt s p).length := by
    rw [length_rmAt s hsc.lt_right]
    have := hsc.lt_right
    omega
  have he := hi.insAt hb (fun x hx => ne_id_of_mem_rmAt hs hsc hx)
    (fun x hx => ne_id_of_mem_rmAt ht htc hx)
    (s[p]'hsc.lt_left).2 (s[p + 1]'hsc.lt_right).2
  have es : ((s[p]'hsc.lt_left).1, (s[p + 1]'hsc.lt_right).2) = s[p + 1]'hsc.lt_right :=
    Prod.ext (hid hsc).symm rfl
  have et : ((t[p]'htc.lt_left).1, (t[p + 1]'htc.lt_right).2) = t[p + 1]'htc.lt_right :=
    Prod.ext (hid htc).symm rfl
  rw [Prod.mk.eta, es, insAt_rmAt s hsc.lt_right] at he
  simpa only [hleft, hright, Prod.mk.eta, et, insAt_rmAt t htc.lt_right] using he

/-- Complete, unique strict-reduced families identify the cap class with the
shorter family. Both maps are chosen from strict realizations; neither a
bijection nor a pairing roundtrip is a premise. -/
theorem cap_representatives_equiv (a b : List (Letter I)) (ε : Bool) (i : I)
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
    ∃ E : {R // R ∈ M ∧
        Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)} ≃
        {S // S ∈ N},
      (∀ R, Iso (pairing₂ (a ++ b) (E R).val)
        (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val) b.length)) ∧
      (∀ S, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) (E.symm S).val)
        (capInsertedPairing a b ε i S.val)) := by
  classical
  let A := a ++ (ε, i) :: (!ε, i) :: b
  let C := {R // R ∈ M ∧ Same (pairing₂ A R) b.length (b.length + 1)}
  have hex (R : C) : ∃ S : {S // S ∈ N},
      Iso (pairing₂ (a ++ b) S.val) (rmAt (pairing₂ A R.val) b.length) := by
    obtain ⟨S, hS, hr, hi⟩ := exists_strictReduced_cap_delete a b ε i
      (hM R R.property.1).1 R.property.2
    obtain ⟨T, hT, hTS⟩ := hNrep S hS hr
    exact ⟨⟨T, hT⟩, hTS.trans hi⟩
  have hey (S : {S // S ∈ N}) : ∃ R : C,
      Iso (pairing₂ A R.val) (capInsertedPairing a b ε i S.val) := by
    obtain ⟨R, hR, hr, hi⟩ := exists_strictReduced_cap_insert a b ε i (hN S S.property).1
    obtain ⟨T, hT, hTR⟩ := hMrep R hR hr
    have hh := hTR.trans hi
    exact ⟨⟨T, hT, (hh.2 _ _).mpr
      (cap_inserted_properties a b ε i (hN S S.property).1).2.2.2.1⟩, hh⟩
  let f := fun R => (hex R).choose
  let g := fun S => (hey S).choose
  have hf (R : C) : Iso (pairing₂ (a ++ b) (f R).val)
      (rmAt (pairing₂ A R.val) b.length) := (hex R).choose_spec
  have hg (S : {S // S ∈ N}) : Iso (pairing₂ A (g S).val)
      (capInsertedPairing a b ε i S.val) := (hey S).choose_spec
  have hgd (S : {S // S ∈ N}) : Iso (rmAt (pairing₂ A (g S).val) b.length)
      (pairing₂ (a ++ b) S.val) := by
    have hi := (hg S).rmAt (g S).property.2.lt_right
    rw [(cap_inserted_properties a b ε i (hN S S.property).1).2.2.2.2] at hi
    exact hi
  have hleft : Function.LeftInverse g f := by
    intro R
    apply Subtype.ext
    apply hMuniq _ (g (f R)).property.1 _ R.property.1
    exact cap_iso_of_deleted (hM _ (g (f R)).property.1).1.pairing_properties.1
      (hM _ R.property.1).1.pairing_properties.1 (g (f R)).property.2 R.property.2
      ((hM _ (g (f R)).property.1).1.pairing_properties.2.2.trans
        (hM _ R.property.1).1.pairing_properties.2.2.symm)
      ((hgd (f R)).trans (hf R))
  have hright : Function.RightInverse g f := by
    intro S
    apply Subtype.ext
    exact hNuniq _ (f (g S)).property _ S.property ((hf (g S)).trans (hgd S))
  exact ⟨⟨f, g, hleft, hright⟩, hf, hg⟩

end OddMath.SKM
