import OddMath.SKM.SpanStrictReduced
import StringDiagrams.Chord.Matching

/-!
# Positive-boundary endpoint pairings

The finite classification used in [BE2, arXiv:1701.04133v2, Theorem 10.3,
proof of Claim 1, p. 41]. We use the existing chord states, their matchings,
and the strictly reduced realizations from §8. This module does not identify
graphical degrees or parities and does not prove the graphical series formula.
-/

namespace OddMath.SKM
open StringDiagrams.Chord

variable {I : Type*} {c d : ℕ}

private def boundaryIndex : Fin c ⊕ Fin d ≃ Fin (c + d) :=
  (Equiv.sumCongr (Fin.revPerm) (Equiv.refl _)).trans finSumFinEquiv

private def boundaryLetter (a : Fin c → I) (b : Fin d → I) : Fin c ⊕ Fin d → Letter I :=
  Sum.elim (fun r => (false, a r)) (fun t => (true, b t))

private theorem boundary_lookup (a : Fin c → I) (b : Fin d → I)
    (x : Fin c ⊕ Fin d) :
    (dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t))[(boundaryIndex x).val]? =
        some (boundaryLetter a b x) := by
  cases x with
  | inl r =>
    have hr : c - 1 - r.val < c := by omega
    have hi : (boundaryIndex (c := c) (d := d) (Sum.inl r)).val = c - 1 - r.val := by
      simp [boundaryIndex, Fin.revPerm, Fin.rev, Nat.sub_sub, Nat.add_comm]
    rw [hi]
    rw [List.getElem?_append_left (by simpa [length_dualW] using hr)]
    unfold dualW
    rw [List.getElem?_reverse (by simpa using hr)]
    simp only [List.length_map, List.length_ofFn]
    have he : c - 1 - (c - 1 - r.val) = r.val := by omega
    rw [he]
    simp [boundaryLetter, flipL]
  | inr t =>
    simp [boundaryIndex, boundaryLetter, dualW]

private theorem boundary_length (a : Fin c → I) (b : Fin d → I)
    {s : List (ℕ × Letter I)}
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t)) : s.length = c + d := by
  have := congrArg List.length hs
  simpa [length_dualW] using this

private theorem boundary_same_letters (a : Fin c → I) (b : Fin d → I)
    {s : List (ℕ × Letter I)} (hl : Lettered flipL s)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t))
    {x y : Fin c ⊕ Fin d} (h : Same s (boundaryIndex x) (boundaryIndex y)) :
    boundaryLetter a b y = flipL (boundaryLetter a b x) := by
  have hh := hl.symm_of_involutive flipL_involutive h
  rw [← Option.map_map] at hh
  rw [← List.getElem?_map, ← List.getElem?_map, hs,
    boundary_lookup, boundary_lookup] at hh
  exact Option.some.inj hh

private theorem exists_right_partner (a : Fin c → I) (b : Fin d → I)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t)) (r : Fin c) :
    ∃ t : Fin d, Same s (boundaryIndex (c := c) (d := d) (Sum.inl r))
      (boundaryIndex (c := c) (d := d) (Sum.inr t)) := by
  let hn := boundary_length a b hs
  let j := matchingOf hv hn (boundaryIndex (c := c) (d := d) (Sum.inl r))
  have hj : Same s (boundaryIndex (c := c) (d := d) (Sum.inl r)) j :=
    (same_iff_matchingOf hv hn _ _).2 rfl
  obtain ⟨y, hy⟩ := boundaryIndex.surjective j
  rw [← hy] at hj
  cases y with
  | inl t =>
    have hh := boundary_same_letters a b hl hs hj
    have := congrArg Prod.fst hh
    simp [boundaryLetter, flipL] at this
  | inr t => exact ⟨t, hj⟩

private theorem exists_left_partner (a : Fin c → I) (b : Fin d → I)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t)) (t : Fin d) :
    ∃ r : Fin c, Same s (boundaryIndex (c := c) (d := d) (Sum.inl r))
      (boundaryIndex (c := c) (d := d) (Sum.inr t)) := by
  let hn := boundary_length a b hs
  let j := matchingOf hv hn (boundaryIndex (c := c) (d := d) (Sum.inr t))
  have hj : Same s (boundaryIndex (c := c) (d := d) (Sum.inr t)) j :=
    (same_iff_matchingOf hv hn _ _).2 rfl
  obtain ⟨y, hy⟩ := boundaryIndex.surjective j
  rw [← hy] at hj
  cases y with
  | inl r => exact ⟨r, hj.symm⟩
  | inr r =>
    have hh := boundary_same_letters a b hl hs hj
    have := congrArg Prod.fst hh
    simp [boundaryLetter, flipL] at this

/-- The finite pairing classification in [BE2, arXiv:1701.04133v2, Theorem 10.3,
proof of Claim 1]. Bottom position `r` is bent to `c - 1 - r.val`; the equivalence
sends bottom positions to top positions (the inverse of the paper's convention).
This statement concerns endpoint pairings, not degrees, parities or the graphical series. -/
theorem positive_pairing_equiv (a : Fin c → I) (b : Fin d → I)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun t => (true, b t)) :
    ∃! e : Fin c ≃ Fin d, (∀ r, a r = b (e r)) ∧
      ∀ r, Same s (c - 1 - r.val) (c + (e r).val) := by
  classical
  let f : Fin c → Fin d := fun r => (exists_right_partner a b hv hl hs r).choose
  have hf (r : Fin c) : Same s (boundaryIndex (c := c) (d := d) (Sum.inl r))
      (boundaryIndex (c := c) (d := d) (Sum.inr (f r))) :=
    (exists_right_partner a b hv hl hs r).choose_spec
  have hinj : Function.Injective f := by
    intro r t h
    have he := hv.unique (hf r).symm (h ▸ (hf t).symm)
    have he' := boundaryIndex.injective (Fin.ext he)
    exact Sum.inl.inj he'
  have hsurj : Function.Surjective f := by
    intro t
    obtain ⟨r, hr⟩ := exists_left_partner a b hv hl hs t
    refine ⟨r, ?_⟩
    have he := hv.unique (hf r) hr
    exact Sum.inr.inj (boundaryIndex.injective (Fin.ext he))
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hf' (r : Fin c) : Same s (c - 1 - r.val) (c + (e r).val) := by
    simpa [boundaryIndex, Fin.revPerm, Fin.rev, Nat.sub_sub, Nat.add_comm, e] using hf r
  refine ⟨e, ⟨?_, hf'⟩, ?_⟩
  · intro r
    have he := congrArg Prod.snd (boundary_same_letters a b hl hs (hf r))
    exact he.symm
  · intro e' he'
    apply Equiv.ext
    intro r
    have he := hv.unique (he'.2 r) (hf' r)
    apply Fin.ext
    change c + (e' r).val = c + (e r).val at he
    omega

private def crossPerm (e : Fin c ≃ Fin d) : Equiv.Perm (Fin c ⊕ Fin d) :=
  (Equiv.sumCongr e e.symm).trans (Equiv.sumComm _ _)

private theorem crossPerm_matching (e : Fin c ≃ Fin d) :
    Function.Involutive (crossPerm e) ∧ ∀ x, crossPerm e x ≠ x := by
  constructor
  · intro x; cases x <;> simp [crossPerm]
  · intro x; cases x <;> simp [crossPerm]

/-- Every colour-preserving boundary equivalence is realized by an existing chord pairing. -/
theorem exists_positive_pairing (a : Fin c → I) (b : Fin d → I)
    (e : Fin c ≃ Fin d) (he : ∀ r, a r = b (e r)) :
    ∃ s : List (ℕ × Letter I), Valid s ∧ Lettered flipL s ∧
      s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
        List.ofFn (fun t => (true, b t)) ∧
      ∀ r, Same s (c - 1 - r.val) (c + (e r).val) := by
  let B : Fin c ⊕ Fin d ≃ Fin (c + d) := boundaryIndex
  let σ := (B.symm.trans (crossPerm e)).trans B
  let lab := fun i => boundaryLetter a b (B.symm i)
  have hσ : IsMatching σ := by
    constructor
    · intro i
      change B (crossPerm e (B.symm (B (crossPerm e (B.symm i))))) = i
      rw [B.symm_apply_apply, (crossPerm_matching e).1, B.apply_symm_apply]
    · intro i hi
      apply (crossPerm_matching e).2 (B.symm i)
      exact B.injective (by simpa [σ] using hi)
  refine ⟨ofMatching σ lab, valid_ofMatching lab hσ, lettered_ofMatching lab hσ ?_, ?_, ?_⟩
  · intro i _
    obtain ⟨x, rfl⟩ := B.surjective i
    cases x with
    | inl r => simp [lab, σ, crossPerm, boundaryLetter, flipL, he r]
    | inr t =>
      have ht := he (e.symm t)
      simp only [e.apply_symm_apply] at ht
      simp [lab, σ, crossPerm, boundaryLetter, flipL, ht]
  · rw [map_snd_ofMatching]
    apply List.ext_getElem (by simp [length_dualW])
    intro i hi hj
    have hi' : i < c + d := by simpa using hi
    obtain ⟨x, hx⟩ := B.surjective ⟨i, hi'⟩
    have hh := boundary_lookup a b x
    have hx' : (boundaryIndex x).val = i := congrArg Fin.val hx
    rw [hx', List.getElem?_eq_getElem hj] at hh
    have hxi : B.symm ⟨i, hi'⟩ = x := by rw [← hx, B.symm_apply_apply]
    simpa [lab, hxi] using (Option.some.inj hh).symm
  · intro r
    have hh := (same_ofMatching lab hσ (B (Sum.inl r)) (B (Sum.inr (e r)))).2
      (by simp [σ, crossPerm])
    simpa [B, boundaryIndex, Fin.revPerm, Fin.rev, Nat.sub_sub, Nat.add_comm] using hh

private theorem iso_of_positive_pairs (a : Fin c → I) (b : Fin d → I)
    {s t : List (ℕ × Letter I)} (hv : Valid s) (hv' : Valid t)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r))
    (ht : t.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r)) (e : Fin c ≃ Fin d)
    (he : ∀ r, Same s (c - 1 - r.val) (c + (e r).val))
    (he' : ∀ r, Same t (c - 1 - r.val) (c + (e r).val)) : Iso s t := by
  have hlen := boundary_length a b hs
  have hlen' := boundary_length a b ht
  have partners (i : ℕ) (hi : i < c + d) : ∃ j, Same s i j ∧ Same t i j := by
    obtain ⟨x, hx⟩ := (boundaryIndex (c := c) (d := d)).surjective ⟨i, hi⟩
    have hx' := congrArg Fin.val hx
    cases x with
    | inl r =>
      have hh : c - 1 - r.val = i := by
        simpa [boundaryIndex, Fin.revPerm, Fin.rev, Nat.sub_sub, Nat.add_comm] using hx'
      exact ⟨c + (e r).val, hh ▸ he r, hh ▸ he' r⟩
    | inr r =>
      have hh : c + r.val = i := by simpa [boundaryIndex] using hx'
      refine ⟨c - 1 - (e.symm r).val, ?_, ?_⟩
      · simpa only [e.apply_symm_apply, hh] using (he (e.symm r)).symm
      · simpa only [e.apply_symm_apply, hh] using (he' (e.symm r)).symm
  refine ⟨hs.trans ht.symm, fun i j => ?_⟩
  constructor
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen] using h.lt_left)
    exact (hv.unique hk h) ▸ hk'
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen'] using h.lt_left)
    exact (hv'.unique hk' h) ▸ hk

/-- The existing two-sided matching has a valid, lettered endpoint pairing. -/
theorem IsMatching₂.pairing_properties {A B : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ A B R) :
    Valid (pairing₂ A R) ∧ Lettered flipL (pairing₂ A R) ∧
      (pairing₂ A R).map Prod.snd = dualW A ++ B := by
  obtain ⟨hf₀, -, -, -⟩ := cupMoves_spec (dualW A)
  refine ⟨((tInv_tStart A).run hR.1).valid,
    lettered_tRun R _ (tInv_tStart A)
      (StringDiagrams.Chord.lettered_run flipL_involutive hf₀) hR.1, ?_⟩
  rw [pairing₂, letters_tRun (length_dualW A) R _ A (tStart_letters A) hR.1, hR.2]

/-- Positive two-sided matchings have equally many bottom and top endpoints. -/
theorem IsMatching₂.positive_length_eq (a : Fin c → I) (b : Fin d → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun t => (true, b t)) R) : c = d := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  obtain ⟨e, -, -⟩ := positive_pairing_equiv a b hv hl hs
  exact Fintype.card_fin c ▸ Fintype.card_fin d ▸ Fintype.card_congr e

/-- The endpoint bijection in [BE2, arXiv:1701.04133v2, Theorem 10.3, proof of
Claim 1], for a set with exactly one representative per reduced pairing class.
The coverage and uniqueness hypotheses spell out the choice of representatives in §8
before Theorem 8.1. No finiteness assumption on that set or on the colours is needed.
The permutations send bottom positions to top positions, inverse to the paper's convention.
This is only the finite classification; no graphical grading or series identity is asserted. -/
theorem positive_representatives_equiv {n : ℕ} (a b : Fin n → I)
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R ∧
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (hrep : ∀ R', IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R' →
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R' →
      ∃ R ∈ M, Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) S) → R = S) :
    ∃ E : {R // R ∈ M} ≃ {w : Equiv.Perm (Fin n) // ∀ r, a r = b (w r)},
      ∀ R r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R.val)
        (n - 1 - r.val) (n + ((E R).val r).val) := by
  classical
  let A := List.ofFn fun r => (true, a r)
  let P (R : {R // R ∈ M}) :=
    positive_pairing_equiv a b (hM R R.property).1.pairing_properties.1
      (hM R R.property).1.pairing_properties.2.1
      (hM R R.property).1.pairing_properties.2.2
  let f : {R // R ∈ M} → {w : Equiv.Perm (Fin n) // ∀ r, a r = b (w r)} :=
    fun R => ⟨(P R).choose, (P R).choose_spec.1.1⟩
  have hf (R : {R // R ∈ M}) (r : Fin n) :
      Same (pairing₂ A R.val) (n - 1 - r.val) (n + ((f R).val r).val) :=
    (P R).choose_spec.1.2 r
  have hinj : Function.Injective f := by
    intro R S h
    apply Subtype.ext
    apply huniq R R.property S S.property
    apply iso_of_positive_pairs a b (hM R R.property).1.pairing_properties.1
      (hM S S.property).1.pairing_properties.1
      (hM R R.property).1.pairing_properties.2.2
      (hM S S.property).1.pairing_properties.2.2 (f R).val (hf R)
    intro r
    rw [h]
    exact hf S r
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨s, hv, hl, hs, hw⟩ := exists_positive_pairing a b w.val w.property
    obtain ⟨R', hR', hred, hiso⟩ := exists_strictReduced_matching hv hl hs
    obtain ⟨R, hR, hRR'⟩ := hrep R' hR' hred
    refine ⟨⟨R, hR⟩, Subtype.ext ?_⟩
    have hRs := hRR'.trans hiso
    have hwR (r : Fin n) : Same (pairing₂ A R) (n - 1 - r.val)
        (n + (w.val r).val) := (hRs.2 _ _).2 (hw r)
    exact ((P ⟨R, hR⟩).choose_spec.2 w.val ⟨w.property, hwR⟩).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end OddMath.SKM
