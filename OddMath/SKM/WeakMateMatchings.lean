import OddMath.SKM.RightMateMatchings
import OddMath.SKM.RightCapAttachment

/-!
# Decorated weakly reduced inverse mates

The source-prefix cups and target-suffix caps used for the upward-to-oriented
reduction in Brundan–Ellis, §8 and Theorem 10.3. These are literal matching
words with transported dot positions; only weak reducedness is asserted.
-/
noncomputable section
namespace OddMath.SKM.WeakMate
open StringDiagrams StringDiagrams.Chord DTMove RightCapAttachment
variable {I : Type*}

def matching (l : List I) (b w : List (Letter I)) (R : List (TMove (Letter I))) :=
  suffixMatching (dns l ++ b) w (cupPrefixMatching l R)

def moves (l : List I) (b w : List (Letter I)) (ds : List (DTMove I)) :=
  suffixMoves (dns l ++ b) w (cupPrefixMoves l ds)

theorem prefix_matching {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R) :
    IsMatching₂ a ((dns l ++ b) ++ w) (cupPrefixMatching l R) := by
  simpa only [List.append_assoc] using (cupPrefix_matching_iso l hR).1

theorem isMatching {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R) :
    IsMatching₂ (a ++ dualW w) (dns l ++ b) (matching l b w R) :=
  suffix_matching (prefix_matching hR)

theorem reduced {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (hr : Reduced₂ (ups l ++ a) R) :
    Reduced₂ (a ++ dualW w) (matching l b w R) :=
  suffix_reduced (prefix_matching hR) (reduced₂_cupPrefix l hR hr)

@[simp] theorem crossings (l : List I) (b w : List (Letter I))
    (R : List (TMove (Letter I))) : ncr₂ (matching l b w R) = ncr₂ R := by
  simp [matching]

@[simp] theorem tmoves_moves (l : List I) (b w : List (Letter I)) (ds : List (DTMove I)) :
    tmoves (moves l b w ds) = matching l b w (tmoves ds) := by
  simp [moves, matching, tmoves_cupPrefix]

def strandEquiv {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R) :
    MatchingStrand (ups l ++ a) R ≃ MatchingStrand (a ++ dualW w) (matching l b w R) :=
  (cupPrefixStrandEquiv l hR).trans (suffixStrandEquiv (prefix_matching hR))

def points {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (q : ℕ → ℕ × ℕ) : ℕ → ℕ × ℕ :=
  suffixPoints (prefix_matching hR) (cupPrefixPoint l ∘ q)

theorem decorates {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (q : ℕ → ℕ × ℕ) (n : MatchingStrand (ups l ++ a) R → ℕ)
    {ds : List (DTMove I)} (hd : Decorates₂ (ups l ++ a) R q (strandCounts n) ds) :
    Decorates₂ (a ++ dualW w) (matching l b w R) (points hR q)
      (strandCounts (n ∘ (strandEquiv hR).symm)) (moves l b w ds) := by
  exact suffix_decorates (prefix_matching hR) _ _ (decorates₂_cupPrefix l hR q n hd)

theorem points_spec {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (ups l ++ a) R,
      (q j).1 ≤ R.length ∧ OnStrand₂ (ups l ++ a) R j (q j))
    (j : MatchingStrand (a ++ dualW w) (matching l b w R)) :
    (points hR q j.val).1 ≤ (matching l b w R).length ∧
      OnStrand₂ (a ++ dualW w) (matching l b w R) j.val (points hR q j.val) := by
  apply suffixPoints_spec (prefix_matching hR)
  intro z hz
  rw [leftEnds₂_cupPrefix l hR] at hz
  exact onStrand₂_cupPrefix l hR (hq z hz).1 (hq z hz).2

/-- The finite dot-count labeling is a bijection, not merely an injection. -/
def dotsEquiv {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R) :
    (MatchingStrand (ups l ++ a) R → ℕ) ≃
      (MatchingStrand (a ++ dualW w) (matching l b w R) → ℕ) :=
  Equiv.arrowCongr (strandEquiv hR) (Equiv.refl ℕ)

theorem dotsEquiv_sum {l : List I} {a b w : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (n : MatchingStrand (ups l ++ a) R → ℕ) :
    ∑ j, dotsEquiv hR n j = ∑ j, n j := (strandEquiv hR).symm.sum_comp n

end OddMath.SKM.WeakMate
