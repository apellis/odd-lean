import OddMath.SKM.CapFamily
import OddMath.SKM.MixedCrossingLocalExamples

/-! Cap-class consumers at an odd colour, in both orientations, with empty
and nonempty shorter boundaries. Every family premise is discharged. -/
noncomputable section
namespace OddMath.SKM.CapFamilyExamples
open StringDiagrams StringDiagrams.Chord

private def a (k : Bool) : List (Letter Bool) := if k then [(true, true)] else []
private def b (k : Bool) : List (Letter Bool) := if k then [(false, true)] else []
private def A (ε k : Bool) := a k ++ (ε, false) :: (!ε, false) :: b k
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) := if k then [.cap 0] else []
private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k}

private theorem hm (ε k : Bool) : IsMatching₂ (A ε k) [] (R k) := by
  cases ε <;> cases k
  · exact ⟨⟨⟨(2, (false, false)), (0, (true, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩

private theorem hn (k : Bool) : IsMatching₂ (a k ++ b k) [] (S k) := by
  cases k
  · exact ⟨trivial, rfl⟩
  · exact ⟨⟨⟨(2, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩

private theorem reducedM (ε k : Bool) : StrictReduced₂ (A ε k) (R k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([4, 6] : List ℕ).Nodup
    simp

private theorem reducedN (k : Bool) : StrictReduced₂ (a k ++ b k) (S k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp

private theorem same_letter {s : List (ℕ × Letter Bool)}
    (hl : Lettered flipL s) {i j : ℕ} (h : Same s i j) :
    (s[j]?).map Prod.snd = ((s[i]?).map Prod.snd).map flipL := by
  rcases lt_or_gt_of_ne h.ne with hij | hji
  · simpa only [Option.map_map] using hl i j h hij
  · have hh := congrArg (Option.map flipL) (hl j i h.symm hji)
    simpa only [Option.map_map, Function.comp_def, flipL_flipL] using hh.symm

private theorem iso_nodup_letters {s t : List (ℕ × Letter Bool)}
    (hs : Valid s) (ht : Valid t) (hls : Lettered flipL s) (hlt : Lettered flipL t)
    (he : s.map Prod.snd = t.map Prod.snd) (hn : (s.map Prod.snd).Nodup) : Iso s t := by
  have forward {u v : List (ℕ × Letter Bool)} (hv : Valid v)
      (hlu : Lettered flipL u) (hlv : Lettered flipL v)
      (he : u.map Prod.snd = v.map Prod.snd) (hn : (v.map Prod.snd).Nodup)
      (i j : ℕ) (h : Same u i j) : Same v i j := by
    have hlen : u.length = v.length := by simpa using congrArg List.length he
    obtain ⟨k, hk, _⟩ := hv i (hlen ▸ h.lt_left)
    have h1 := same_letter hlu h
    have h2 := same_letter hlv hk
    simp only [← List.getElem?_map] at h1 h2
    rw [he] at h1
    have hj := h.lt_right
    have hjk : j = k := (List.Nodup.getElem?_inj (by simp only [List.length_map]; omega) hn).mp
      (h1.trans h2.symm)
    exact hjk ▸ hk
  exact ⟨he, fun i j => ⟨forward ht hls hlt he (he ▸ hn) i j,
    forward hs hlt hls he.symm hn i j⟩⟩

private theorem hM (ε k : Bool) : ∀ V ∈ M k,
    IsMatching₂ (A ε k) [] V ∧ StrictReduced₂ (A ε k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hm ε k, reducedM ε k⟩

private theorem hN (k : Bool) : ∀ V ∈ N k,
    IsMatching₂ (a k ++ b k) [] V ∧ StrictReduced₂ (a k ++ b k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hn k, reducedN k⟩

private theorem hMrep (ε k : Bool) : ∀ V, IsMatching₂ (A ε k) [] V →
    StrictReduced₂ (A ε k) V → ∃ W ∈ M k, Iso (pairing₂ (A ε k) W) (pairing₂ (A ε k) V) := by
  intro V h _
  refine ⟨R k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hm ε k).pairing_properties.1 h.pairing_properties.1
    (hm ε k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hm ε k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hm ε k).pairing_properties.2.2]
  cases ε <;> cases k <;> decide

private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (a k ++ b k) [] V →
    StrictReduced₂ (a k ++ b k) V →
    ∃ W ∈ N k, Iso (pairing₂ (a k ++ b k) W) (pairing₂ (a k ++ b k) V) := by
  intro V h _
  refine ⟨S k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hn k).pairing_properties.1 h.pairing_properties.1
    (hn k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hn k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hn k).pairing_properties.2.2]
  cases k <;> decide

private theorem cap (ε k : Bool) :
    Same (pairing₂ (A ε k) (R k)) (b k).length ((b k).length + 1) := by
  cases ε <;> cases k <;> unfold Same idAt <;> decide

private def E (ε k : Bool) :
    {V // V ∈ M k ∧ Same (pairing₂ (A ε k) V) (b k).length ((b k).length + 1)} ≃
    {W // W ∈ N k} :=
  (cap_representatives_equiv (a k) (b k) ε false (M k) (N k) (hM ε k) (hN k)
    (hMrep ε k) (hNrep k)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)).choose

/-- Both cap orientations, including a nonzero reversed insertion position,
use the constructed representative equivalence at a verified odd colour. -/
theorem odd_cap_roundtrips (ε k : Bool) :
    MixedCrossingLocalExamples.oddDatum.parity false = 1 ∧
    (E ε k).symm (E ε k ⟨R k, Set.mem_singleton _, cap ε k⟩) =
      ⟨R k, Set.mem_singleton _, cap ε k⟩ ∧
    E ε k ((E ε k).symm ⟨S k, Set.mem_singleton _⟩) = ⟨S k, Set.mem_singleton _⟩ :=
  ⟨rfl, (E ε k).symm_apply_apply _, (E ε k).apply_symm_apply _⟩

/-- The forward and inverse maps realize removal and insertion, including letters. -/
theorem odd_cap_pairings (ε k : Bool) :
    (∀ V, Iso (pairing₂ (a k ++ b k) (E ε k V).val)
      (rmAt (pairing₂ (A ε k) V.val) (b k).length)) ∧
    (∀ W, Iso (pairing₂ (A ε k) ((E ε k).symm W).val)
      (capInsertedPairing (a k) (b k) ε false W.val)) :=
  (cap_representatives_equiv (a k) (b k) ε false (M k) (N k) (hM ε k) (hN k)
    (hMrep ε k) (hNrep k)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)).choose_spec

end OddMath.SKM.CapFamilyExamples
