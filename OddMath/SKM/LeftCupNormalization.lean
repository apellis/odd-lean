import OddMath.SKM.LeftCupAttachment
import OddMath.SKM.DecoratedNormalization

/-! # Normalized decorated left-cup transport

BE2, arXiv:1701.04133v2, §8 and Theorem 10.3 Claim 3.
Compare a chosen reduced target with the literal left-cup attachment using the
existing decorated reduced-representative comparison. The region weight is
`wt D μ a`, after removing the downward left-cons letter. This proves the
numerical transport, not the graphical-series or bilinear-form equality.
-/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I X : Type*} [AddCommGroup X]

/-- The normalized left cup has degree shift `dᵢ(1−hᵢν)` and parity shift `|i,ν|`.
Matching, crossing-minimality, pairing isomorphism and independently chosen
point decorations are explicit. Source points retain their height bounds.
Only `Reduced₂` is used; no strict critical-point preservation is asserted. -/
theorem leftCupAttach_normalized_decorated_degree_parity
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ ((false, i) :: a) b R) (hrR : Reduced₂ ((false, i) :: a) R)
    (hS : IsMatching₂ a ((true, i) :: b) S) (hrS : Reduced₂ a S)
    (hi : Iso (pairing₂ ((false, i) :: a) R) (pairing₂ a S))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ ((false, i) :: a) R,
      (q j).1 ≤ R.length ∧ OnStrand₂ ((false, i) :: a) R j (q j))
    (hr : ∀ j ∈ leftEnds₂ a S, OnStrand₂ a S j (r j))
    (c : MatchingStrand ((false, i) :: a) R → ℕ) (ds es : List (DTMove I))
    (hd : Decorates₂ ((false, i) :: a) R q (strandCounts c) ds)
    (he : Decorates₂ a S r (strandCounts (c ∘ (matchingStrandEquivOfIso hi).symm)) es) :
    tableDegree D sy μ (dLay a es) = tableDegree D sy μ (dLay ((false, i) :: a) ds) +
      sy.d i * (1 - D.h i (wt D μ a)) ∧
    xpar D μ (dLay a es) = xpar D μ (dLay ((false, i) :: a) ds) +
      ipar D i (wt D μ a) := by
  obtain ⟨hm, hc⟩ := leftCupAttach_matching_iso hR
  let hi' := hc.trans hi
  have hq' : ∀ j ∈ leftEnds₂ a (leftCupAttachMatching i R),
      OnStrand₂ a (leftCupAttachMatching i R) j ((cupAttachPoint ∘ q) j) := by
    intro j hj
    change j ∈ leftEnds₂ a (CupAttachment.cupAttachMatching true i R) at hj
    rw [CupAttachment.leftEnds₂_cupAttach (o := true) hR] at hj
    exact (CupAttachment.onStrand₂_cupAttach (o := true) hR (hq j hj).1 (hq j hj).2).2
  have hcounts : (c ∘ (CupAttachment.cupAttachStrandEquiv (o := true) hR).symm) ∘
      (matchingStrandEquivOfIso hi').symm = c ∘ (matchingStrandEquivOfIso hi).symm := by
    funext j
    rfl
  have he' : Decorates₂ a S r
      (strandCounts ((c ∘ (CupAttachment.cupAttachStrandEquiv (o := true) hR).symm) ∘
        (matchingStrandEquivOfIso hi').symm)) es := by rw [hcounts]; exact he
  obtain ⟨hdeg, hpar⟩ := mixed_decorated_degree_parity_of_iso D sy μ
    hm (reduced₂_leftCupAttach hR hrR) hS hrS hi' (cupAttachPoint ∘ q) r hq' hr
    (c ∘ (CupAttachment.cupAttachStrandEquiv (o := true) hR).symm)
    (leftCupAttachMoves i ds) es (CupAttachment.decorates₂_cupAttach (o := true) hR q c hd) he'
  obtain ⟨hraw, hpraw⟩ := leftCupAttach_degree_parity D sy μ hR hd.1
  exact ⟨hdeg.symm.trans hraw, hpar.symm.trans hpraw⟩

end OddMath.SKM
