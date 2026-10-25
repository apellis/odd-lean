import OddMath.SKM.PairingRotation

namespace OddMath.SKM.PairingRotationExamples
open StringDiagrams StringDiagrams.Chord RightCapAttachment

private theorem identity_matching (a : List (Letter Bool)) : IsMatching₂ a a [] :=
  ⟨trivial, rfl⟩

example : Valid ((pairing₂ [up true] []).rotate 1) :=
  (identity_matching [up true]).pairing_properties.1.rotate 1

example : Lettered flipL ((pairing₂ [up true] []).rotate 1) :=
  (identity_matching [up true]).pairing_properties.2.1.rotate flipL_involutive 1

example : Iso (pairing₂ [up true] []) (pairing₂ [up true] []) :=
  (iso_rotate_iff _ _ 37).mp (Iso.refl _)

example : Iso
    (pairing₂ ([up true, dn false] ++ dualW [up true, dn false])
      (suffixMatching [] [up true, dn false] []))
    ((pairing₂ [up true, dn false] []).rotate
      ((pairing₂ [up true, dn false] []).length - 2)) :=
  suffix_pairing_rotate (a := [up true, dn false]) (b := [])
    (w := [up true, dn false]) (identity_matching [up true, dn false])

example : ∃ R, IsMatching₂ [] ([dn true] ++ [up true]) R ∧ StrictReduced₂ [] R ∧
    Iso (pairing₂ ([] ++ dualW [up true]) (suffixMatching [dn true] [up true] R))
      (pairing₂ ([] ++ dualW [up true]) []) := by
  apply exists_strict_suffix_preimage
  simpa using identity_matching [dn true]

#print axioms StringDiagrams.Chord.iso_rotate_iff
#print axioms StringDiagrams.Chord.valid_rotate_iff
#print axioms StringDiagrams.Chord.lettered_rotate_iff
#print axioms OddMath.SKM.RightCapAttachment.suffix_pairing_rotate
#print axioms OddMath.SKM.RightCapAttachment.suffix_pairing_iso_iff
#print axioms OddMath.SKM.RightCapAttachment.exists_strict_suffix_preimage

end OddMath.SKM.PairingRotationExamples
