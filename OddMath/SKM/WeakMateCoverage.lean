import OddMath.SKM.WeakMateMatchings
import OddMath.SKM.PairingRotation
import OddMath.SKM.MatchingBending

/-! Pairing coverage and reflection for the literal inverse mates in the
Brundan–Ellis §8 upward-to-oriented reduction. -/
namespace OddMath.SKM.WeakMate
open StringDiagrams StringDiagrams.Chord RightCapAttachment
variable {I : Type*}

theorem pairing_iso_iff {l : List I} {a b w : List (Letter I)}
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (ups l ++ a) (b ++ w) R)
    (hS : IsMatching₂ (ups l ++ a) (b ++ w) S) :
    Iso (pairing₂ (a ++ dualW w) (matching l b w R))
      (pairing₂ (a ++ dualW w) (matching l b w S)) ↔
      Iso (pairing₂ (ups l ++ a) R) (pairing₂ (ups l ++ a) S) := by
  have hr := (cupPrefix_matching_iso l hR).2
  have hs := (cupPrefix_matching_iso l hS).2
  have ht := suffix_pairing_iso_iff (prefix_matching hR) (prefix_matching hS)
  change Iso (pairing₂ (a ++ dualW w) (suffixMatching (dns l ++ b) w (cupPrefixMatching l R)))
    (pairing₂ (a ++ dualW w) (suffixMatching (dns l ++ b) w (cupPrefixMatching l S))) ↔ _
  exact ⟨fun h => hr.symm.trans ((ht.mp h).trans hs),
    fun h => ht.mpr (hr.trans (h.trans hs.symm))⟩

theorem exists_strict_preimage {l : List I} {a b w : List (Letter I)}
    {S : List (TMove (Letter I))} (hS : IsMatching₂ (a ++ dualW w) (dns l ++ b) S) :
    ∃ R, IsMatching₂ (ups l ++ a) (b ++ w) R ∧ StrictReduced₂ (ups l ++ a) R ∧
      Iso (pairing₂ (a ++ dualW w) (matching l b w R))
        (pairing₂ (a ++ dualW w) S) := by
  obtain ⟨R₀, hR₀, _, hi₀⟩ := exists_strict_suffix_preimage hS
  obtain ⟨hv, hl, hs⟩ := hR₀.pairing_properties
  have hb : dualW (ups l ++ a) ++ (b ++ w) = dualW a ++ ((dns l ++ b) ++ w) := by
    rw [dualW_append]
    simp [dualW, ups, dns, List.map_map, Function.comp_def, List.append_assoc, flipL]
  obtain ⟨R, hR, hred, hi⟩ := exists_strictReduced_matching hv hl (hs.trans hb.symm)
  have hc := (cupPrefix_matching_iso l hR).2.trans hi
  have hf := (suffix_pairing_iso_iff (prefix_matching hR) hR₀).mpr hc
  exact ⟨R, hR, hred, hf.trans hi₀⟩

end OddMath.SKM.WeakMate
