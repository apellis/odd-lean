import OddMath.SKM.RightClosure
import OddMath.SKM.CupAttachmentReduced

/-!
# Matching syntax for partial right mates

Iterated literal right-cup attachment for the upward-to-oriented reduction
of Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. This is the source-prefix
half of `partialRightMateL`. Weak reducedness is preserved; no preservation
of the stricter critical-point condition is claimed.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

/-- Bend an upward source prefix to a downward target prefix, one letter
at a time. -/
def cupPrefixMatching : List I → List (TMove (Letter I)) → List (TMove (Letter I))
  | [], R => R
  | i :: l, R => cupPrefixMatching l (cupAttachMatching i R)

def cupPrefixMoves : List I → List (DTMove I) → List (DTMove I)
  | [], ds => ds
  | i :: l, ds => cupPrefixMoves l (cupAttachMoves i ds)

/-- The recursively attached ordinary layers. -/
def cupPrefixLayers : List I → List (Letter I) → List (LayerData I) → List (LayerData I)
  | [], _, L => L
  | i :: l, a, L => cupPrefixLayers l a (cupAttachLayers i (ups l ++ a) L)

theorem cupPrefixLayers_eq (l : List I) (a : List (Letter I)) (L : List (LayerData I)) :
    cupPrefixLayers l a L =
      (cupN l).map (whL [] a) ++ L.map (whL (dns l) []) := by
  induction l generalizing L with
  | nil => simp [cupPrefixLayers, cupN, dns]
  | cons i l ih =>
    simp [cupPrefixLayers, ih, cupAttachLayers, cupN, dns, ups, whL, List.append_assoc]

theorem cupPrefixLayers_eq_partialMate (l : List I) (a b : List (Letter I))
    (L : List (LayerData I)) :
    cupPrefixLayers l a L = partialRightMateL l [] a b L := by
  simp [cupPrefixLayers_eq, partialRightMateL, dns, capN]

theorem sChain_cupPrefixLayers (l : List I) {a b : List (Letter I)}
    {L : List (LayerData I)} (hL : SChain (ups l ++ a) L b) :
    SChain a (cupPrefixLayers l a L) (dns l ++ b) := by
  rw [cupPrefixLayers_eq_partialMate l a b]
  simpa [ups] using sChain_partialRightMateL l [] a b (by simpa [ups] using hL)

theorem cupPrefix_matching_iso (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R) :
    IsMatching₂ a (dns l ++ b) (cupPrefixMatching l R) ∧
      Iso (pairing₂ a (cupPrefixMatching l R)) (pairing₂ (ups l ++ a) R) := by
  induction l generalizing b R with
  | nil => exact ⟨hR, Iso.refl _⟩
  | cons i l ih =>
    obtain ⟨hm, hi⟩ := cupAttach_matching_iso hR
    obtain ⟨hm', hi'⟩ := ih hm
    refine ⟨?_, hi'.trans hi⟩
    simpa [cupPrefixMatching, dns, List.append_assoc] using hm'

theorem reduced₂_cupPrefix (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R)
    (hr : Reduced₂ (ups l ++ a) R) : Reduced₂ a (cupPrefixMatching l R) := by
  induction l generalizing b R with
  | nil => exact hr
  | cons i l ih =>
    exact ih (cupAttach_matching_iso hR).1 (reduced₂_cupAttach hR hr)

@[simp] theorem ncr₂_cupPrefix (l : List I) (R : List (TMove (Letter I))) :
    ncr₂ (cupPrefixMatching l R) = ncr₂ R := by
  induction l generalizing R with
  | nil => rfl
  | cons i l ih => simp [cupPrefixMatching, ih]

theorem leftEnds₂_cupPrefix (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R) :
    leftEnds₂ a (cupPrefixMatching l R) = leftEnds₂ (ups l ++ a) R := by
  classical
  have hi := (cupPrefix_matching_iso l hR).2
  unfold leftEnds₂
  rw [hi.length_eq]
  congr 1
  funext j
  simp only [isLeftEnd_iso hi]

/-- Source-prefix bending keeps the ordered strand labels themselves. -/
def cupPrefixStrandEquiv (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R) :
    MatchingStrand (ups l ++ a) R ≃ MatchingStrand a (cupPrefixMatching l R) where
  toFun j := ⟨j.val, by rw [leftEnds₂_cupPrefix l hR]; exact j.property⟩
  invFun j := ⟨j.val, by rw [← leftEnds₂_cupPrefix l hR]; exact j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem cupPrefixStrandEquiv_val (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R)
    (j : MatchingStrand (ups l ++ a) R) : (cupPrefixStrandEquiv l hR j).val = j.val := rfl

theorem tmoves_cupPrefix (l : List I) (ds : List (DTMove I)) :
    tmoves (cupPrefixMoves l ds) = cupPrefixMatching l (tmoves ds) := by
  induction l generalizing ds with
  | nil => rfl
  | cons i l ih =>
    simp [cupPrefixMoves, cupPrefixMatching, ih, cupAttachMoves, cupAttachMatching,
      tmoves, tmoves_map_shiftD]

/-- The position and height both increase by the number of attached cups. -/
def cupPrefixPoint (l : List I) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + l.length, p.2 + l.length)

theorem dotPts_cupPrefix (l : List I) (ds : List (DTMove I)) :
    dotPts (cupPrefixMoves l ds) = (dotPts ds).map (cupPrefixPoint l) := by
  induction l generalizing ds with
  | nil =>
    have h : cupPrefixPoint ([] : List I) = id := by
      funext p
      simp [cupPrefixPoint]
    simp [cupPrefixMoves, h]
  | cons i l ih =>
    simp [cupPrefixMoves, ih, List.map_map, Function.comp_def, cupPrefixPoint,
      cupAttachPoint, Nat.add_comm, Nat.add_left_comm]

/-- Replicated distinguished points and every strand-dot count are transported
by the literal matching construction, without choosing a new serializer. -/
theorem decorates₂_cupPrefix (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R)
    (q : ℕ → ℕ × ℕ) (c : MatchingStrand (ups l ++ a) R → ℕ)
    {ds : List (DTMove I)} (hd : Decorates₂ (ups l ++ a) R q (strandCounts c) ds) :
    Decorates₂ a (cupPrefixMatching l R) (cupPrefixPoint l ∘ q)
      (strandCounts (c ∘ (cupPrefixStrandEquiv l hR).symm)) (cupPrefixMoves l ds) := by
  classical
  constructor
  · rw [tmoves_cupPrefix, hd.1]
  · rw [dotPts_cupPrefix]
    have hp := hd.2.map (cupPrefixPoint l)
    rw [List.map_flatMap] at hp
    refine hp.trans (List.Perm.of_eq ?_)
    rw [leftEnds₂_cupPrefix l hR]
    apply List.flatMap_congr
    intro j hj
    have hj' : j ∈ leftEnds₂ a (cupPrefixMatching l R) := by
      rw [leftEnds₂_cupPrefix l hR]
      exact hj
    simp [List.map_replicate, strandCounts, hj, hj', cupPrefixStrandEquiv]

theorem onStrand₂_cupPrefix (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R)
    {j : ℕ} {p : ℕ × ℕ} (hbound : p.1 ≤ R.length)
    (hp : OnStrand₂ (ups l ++ a) R j p) :
    (cupPrefixPoint l p).1 ≤ (cupPrefixMatching l R).length ∧
      OnStrand₂ a (cupPrefixMatching l R) j (cupPrefixPoint l p) := by
  induction l generalizing b R p with
  | nil => exact ⟨hbound, hp⟩
  | cons i l ih =>
    obtain ⟨hbound', hp'⟩ := onStrand₂_cupAttach hR hbound hp
    have H := ih (cupAttach_matching_iso hR).1 hbound' hp'
    simpa [cupPrefixMatching, cupPrefixPoint, cupAttachPoint,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

theorem dLay_cupPrefix (l : List I) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R)
    {L : List (LayerData I)} (he : L.map ofL = dLay (ups l ++ a) ds) :
    (cupPrefixLayers l a L).map ofL = dLay a (cupPrefixMoves l ds) := by
  induction l generalizing b R ds L with
  | nil => exact he
  | cons i l ih =>
    apply ih (cupAttach_matching_iso hR).1
    · simpa [cupAttachMoves, cupAttachMatching, tmoves, tmoves_map_shiftD] using
        congrArg (cupAttachMatching i) hd
    · rw [dLay_cupAttach (a := ups l ++ a) hR hd]
      have he' : L.map ofL = dLay ((true, i) :: (ups l ++ a)) ds := he
      rw [← he', map_xwhL_map_ofL]
      rfl

section Evaluation
variable {X : Type*} [AddCommGroup X] {D : Datum I X}
  {k : Type*} [CommRing k] (Sc : Scalars D k)

/-- The matching-syntax source-prefix construction is recovered by the
native right closure; no right closing word or bubble transport is needed. -/
theorem cl_rightClosure_cupPrefix (μ : X) (l : List I) {a b : List (Letter I)}
    {L : List (LayerData I)} (hL : SChain (ups l ++ a) L b) :
    cl D Sc μ (ups l ++ a) (b ++ ups [])
      (rightClosureL l [] a b (cupPrefixLayers l a L)) =
    cl D Sc μ (ups l ++ a) (b ++ ups []) L := by
  rw [cupPrefixLayers_eq_partialMate l a b]
  exact cl_rightClosure_partialMate Sc μ l [] a b (by simpa [ups] using hL)
end Evaluation

end OddMath.SKM
